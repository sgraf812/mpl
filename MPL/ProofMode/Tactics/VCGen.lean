/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
import MPL.ProofMode.Tactics.Basic
import MPL.WPSimp
import MPL.WP
import MPL.WPMonad
import MPL.WPMonadLift
import MPL.WPMonadFunctor
import MPL.WPMonadExceptOf

import MPL.ProofMode.Tactics.Intro
import MPL.ProofMode.Tactics.WP
import MPL.ProofMode.Tactics.Spec
import MPL.Triple

/-!
# Tactic `mvcgen`
-/

namespace MPL.ProofMode.Tactics
open Lean Elab Tactic Meta

initialize registerTraceClass `mpl.tactics.vcgen

namespace VC

inductive ProofTerm where
| rfl
| nonrfl (e : Expr)

inductive Fuel where
| limited (n : Nat)
| unlimited
deriving DecidableEq

def Fuel.burnOne (fuel : Fuel) : Option Fuel :=
  match fuel with
  | Fuel.limited 0 => none
  | Fuel.limited n => some (Fuel.limited (n - 1))
  | Fuel.unlimited => Fuel.unlimited

partial def step (fuel : Fuel) (goal : MGoal) (subst : Array Expr) (discharge : MGoal → Array Expr → MetaM Expr) : MetaM (Fuel × Expr) := do
  let some fuel := fuel.burnOne | return (fuel, ← discharge goal subst)
  let T := goal.target.consumeMData
  trace[mpl.tactics.vcgen] "target: {T}"
  logInfo m!"target: {T}"
  if let some _ := T.app3? ``SPred.imp then
    return ← onImp
  if T.isAppOf ``PredTrans.apply then
    return ← onApply
  return (fuel, ← discharge goal subst)
where
  onImp := do mIntro goal (← `(binderIdent| _)) (fun g => step fuel g subst discharge)

  onApply := do
    let args := goal.target.getAppArgs
    let wp := args[2]!
    let Q := args[3]!
    match_expr wp with
    | WP.wp m ps instWP α e =>
      let us := wp.getAppFn.constLevels!
      if let .letE x ty val body _nonDep := e then
        return (fuel, ← withLetDecl x ty val fun fv => do
        let subst := subst.push fv
        let wp' := mkApp5 (mkConst ``WP.wp us) m ps instWP α body
        let args' := args.set! 2 wp'
        let goal := { goal with target := mkAppN (mkConst ``PredTrans.apply) args' }
        mkLetFVars #[fv] (← discharge goal subst))
      logInfo m!"hyps: {(← getLocalHyps)}"
      logInfo m!"e: {e}"
      if e.isIte then
        let ite_args := e.getAppArgs
        -- TODO: Only do this if Q is not already a var
        let Qty := mkApp2 (mkConst ``PostCond) α ps
        return (fuel, ← withLetDecl `Q Qty Q fun Q => do
        let t := mkApp5 (mkConst ``WP.wp us) m ps instWP α (e.getArg! 3)
        let e := mkApp5 (mkConst ``WP.wp us) m ps instWP α (e.getArg! 4)
        let tapplyQ := mkAppN (mkConst ``PredTrans.apply) (args.set! 2 t |>.set! 3 Q)
        let eapplyQ := mkAppN (mkConst ``PredTrans.apply) (args.set! 2 e |>.set! 3 Q)
        let ret_ty := (← inferType tapplyQ)
        let u ← getLevel ret_ty
        let ite_args' := ite_args.set! 0 (← inferType tapplyQ) |>.set! 3 tapplyQ |>.set! 4 eapplyQ
        let ite := mkAppN (mkConst ``ite [u]) ite_args'
        let goal := { goal with target := ite }
        mkLetFVars #[Q] (← discharge goal subst))
      if e.isAppOf ``Pure.pure then
        return (fuel, ← withLetDecl `a α (e.getArg! 3) fun a => do
        let goal := { goal with target := mkAppN (mkApp (mkProj ``Prod 0 Q) a) args }
        mkLetFVars #[a] (← discharge goal subst))
      -- Split match-expressions
      if let some info := isMatcherAppCore? (← getEnv) e then
        let candidate ← id do
          let args := e.getAppArgs
          logInfo "e: {e}, args: {args}"
          for i in [info.getFirstDiscrPos : info.getFirstDiscrPos + info.numDiscrs] do
            if args[i]!.hasLooseBVars then
              return false
          return true
        if candidate then
          -- We could be even more deliberate here and use the `lifter` lemmas
          -- for the match statements instead of the `split` tactic.
          -- For now using `splitMatch` works fine.
          -- return ← Split.splitMatch goal e
          return (fuel, ← discharge goal subst)
    | _ => return (fuel, ← discharge goal subst)
--    if wp.isAppOf ``WP.wp then
--      let_expr WP.wp m ps instWP α x := wp | throwError "target not a wp application {wp}"
--    match
  return (fuel, ← discharge goal subst)

end VC

elab "mvcgen_step" n:(num)? : tactic => do
  let n := n.map (·.raw.toNat) |>.getD 1
  let (mvar, goal) ← mStart (← getMainGoal)
  mvar.withContext do
  let goals ← IO.mkRef []
  mvar.assign (← Prod.snd <$> VC.step (fuel := .limited n) goal #[] fun hyp subst => do
    let m ← mkFreshExprSyntheticOpaqueMVar (hyp.toExpr.instantiateRev subst)
    goals.modify (m.mvarId! :: ·)
    return m)
  replaceMainGoal (← goals.get)

elab "mvcgen" : tactic => do
  let (mvar, goal) ← mStart (← getMainGoal)
  mvar.withContext do
  let goals ← IO.mkRef []
  mvar.assign (← Prod.snd <$> VC.step (fuel := .unlimited) goal #[] fun hyp subst => do
    let m ← mkFreshExprSyntheticOpaqueMVar (hyp.toExpr.instantiateRev subst)
    goals.modify (m.mvarId! :: ·)
    return m)
  replaceMainGoal (← goals.get)

def fib_impl (n : Nat) : Idd Nat := do
  if n = 0 then return 0
  let mut a := 0
  let mut b := 1
  for _ in [1:n] do
    let a' := a
    a := b
    b := a' + b
  return b

abbrev fib_spec : Nat → Nat
| 0 => 0
| 1 => 1
| n+2 => fib_spec n + fib_spec (n+1)

theorem fib_triple : ⦃⌜True⌝⦄ fib_impl n ⦃⇓ r => r = fib_spec n⦄ := by
  unfold fib_impl
  dsimp
  mintro _
  if h : n = 0 then simp [h] else
  simp only [h]
  mwp
  mspec Specs.forIn_list (⇓ (⟨a, b⟩, xs) => a = fib_spec xs.rpref.length ∧ b = fib_spec (xs.rpref.length + 1)) ?step
  case step => dsimp; intros; mintro _; mwp; simp_all
  simp_all [Nat.sub_one_add_one]

theorem fib_triple_vc : ⦃⌜True⌝⦄ fib_impl n ⦃⇓ r => r = fib_spec n⦄ := by
  unfold fib_impl
  mvcgen_step 3
--  dsimp
--  mintro _
--  if h : n = 0 then simp [h] else
--  simp only [h]
--  mwp
--  mspec Specs.forIn_list (⇓ (⟨a, b⟩, xs) => a = fib_spec xs.rpref.length ∧ b = fib_spec (xs.rpref.length + 1)) ?step
--  case step => dsimp; intros; mintro _; mwp; simp_all
--  simp_all [Nat.sub_one_add_one]
