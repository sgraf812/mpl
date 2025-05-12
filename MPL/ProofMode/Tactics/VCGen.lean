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
import MPL.ProofMode.Tactics.Cases
import MPL.ProofMode.Tactics.Specialize
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

theorem Specs.ite_pre {m} (c : Prop) [Decidable c] (t : m α) (e : m α)
    {ps} [WP m ps] {P : Assertion ps} {Q₁ Q₂ : PostCond α ps}
    (ht : c → ⦃P⦄ t ⦃Q₁⦄) (he : ¬c → ⦃P⦄ e ⦃Q₂⦄) :
    ⦃P⦄ if c then t else e ⦃if c then Q₁ else Q₂⦄ := by
  split <;> apply_rules

theorem Specs.ite_post {m} (c : Prop) [Decidable c] (t : m α) (e : m α)
    {ps} [WP m ps] {P₁ P₂ : Assertion ps} {Q : PostCond α ps}
    (ht : c → ⦃P₁⦄ t ⦃Q⦄) (he : ¬c → ⦃P₂⦄ e ⦃Q⦄) :
    ⦃if c then P₁ else P₂⦄ if c then t else e ⦃Q⦄ := by
  split <;> apply_rules

theorem split_ite {α m ps} {P : Assertion ps} {Q : PostCond α ps} (c : Prop) [Decidable c] [WP m ps] (t : m α) (e : m α)
    (ht : c → ⦃P⦄ t ⦃Q⦄) (he : ¬c → ⦃P⦄ e ⦃Q⦄) :
    ⦃P⦄ if c then t else e ⦃Q⦄ := by
  split <;> apply_rules

theorem Specs.bind_pre [Monad m] [WPMonad m ps] {x : m α} {f : α → m β} {P : Assertion ps} {Q : PostCond β ps}
    (h : ⦃P⦄ x ⦃(fun a => wp⟦f a⟧.apply Q, Q.2)⦄) :
    ⦃P⦄ (x >>= f) ⦃Q⦄ := by
  mintro _
  mwp
  exact h

inductive Fuel where
| limited (n : Nat)
| unlimited
deriving DecidableEq

structure State where
  fuel : Fuel := .unlimited

abbrev VCGenM := StateRefT State MetaM

def burnOne : VCGenM PUnit := do
  let s ← get
  match s.fuel with
  | Fuel.limited 0 => return ()
  | Fuel.limited (n + 1) => set { s with fuel := .limited n }
  | Fuel.unlimited => return ()

def ifOutOfFuel (x : VCGenM α) (k : VCGenM α) : VCGenM α := do
  let s ← get
  match s.fuel with
  | Fuel.limited 0 => x
  | _ => k

structure Result where
--  expr : Expr
  proof? : Option Expr := none

def isTrivial (e : Expr) : Bool := match e with
  | .bvar .. => true
  | .mvar .. => true
  | .fvar .. => true
  | .const .. => true
  | .lit .. => true
  | .sort .. => true
  | .mdata _ e => isTrivial e
  | .proj _ _ e => isTrivial e
  | .lam .. => false
  | .forallE .. => false
  | .letE .. => false
  | .app .. => false

def withNonTrivialLetDecl (name : Name) (type : Expr) (val : Expr) (k : Expr → (Expr → VCGenM Expr) → VCGenM α) (kind : LocalDeclKind := .default) : VCGenM α :=
  if isTrivial val then
    k val pure
  else
    withLetDecl name type val (kind := kind) fun fv => do
      k fv (liftM <| mkForallFVars #[fv] ·)

partial def step (fuel : Fuel) (goal : MGoal) (subst : Array Expr) (discharge : Expr → Array Expr → VCGenM Expr) : MetaM Expr :=
  StateRefT'.run' (onGoal goal subst) { fuel }
where
  onFail (goal : MGoal) (subst : Array Expr) : VCGenM Expr := do
    logInfo m!"onFail: {goal.toExpr}, subst: {subst}, substituted: {goal.toExpr.instantiate subst}"
    return ← discharge goal.toExpr subst

  -- TODO: Update
  -- If `let { expr, proof? } := onGoal goal subst`,
  -- then `expr` is defeq to `goal.toExpr` (modulo `subst`)
  -- and `proof` is the proof of the goal.
  -- TODO: Figure otu what to do with `none`
  onGoal goal subst : VCGenM Expr := do
    -- trace[mpl.tactics.vcgen] "target: {T}"
    -- logInfo m!"target: {T}"
    let f := goal.target.consumeMData.getAppFn
    match f.constName? with
    | some ``SPred.imp => onImp goal subst
    | some ``PredTrans.apply => onApply goal subst
    | _ => onFail goal subst

  onImp goal subst : VCGenM Expr := ifOutOfFuel (onFail goal subst) do
    burnOne
    (·.2) <$> mIntro goal (← `(binderIdent| _)) (fun g =>
        do return ((), ← onGoal g subst))

  onApply goal subst : VCGenM Expr := ifOutOfFuel (onFail goal subst) do
    let args := goal.target.getAppArgs
    let trans := args[2]!
    let Q := args[3]!
    logInfo m!"apply: {trans}"
    match_expr trans with
    | WP.wp m ps instWP α e =>
      let us := trans.getAppFn.constLevels!
      let u := us[0]!
      if let .letE x ty val body _nonDep := e then
        burnOne
        return ← withNonTrivialLetDecl x ty val fun fv leave => do
        let subst := subst.push fv
        let wp' := mkApp5 (mkConst ``WP.wp us) m ps instWP α body
        let args' := args.set! 2 wp'
        let goal := { goal with target := mkAppN (mkConst ``PredTrans.apply) args' }
        leave (← onApply goal subst)
      let monad? ← OptionT.run do
        let instMon ← OptionT.mk <| synthInstance? (mkApp (mkConst ``Monad [Level.zero, u])  m)
        let instWPMon ← OptionT.mk <| synthInstance? (mkApp3 (mkConst ``WPMonad us) m ps instMon)
        return (instMon, instWPMon)
      match_expr e with
      | ite α c instDec th el =>
        burnOne
        -- TODO: This duplicates Q. We should compute the strongest post for goal.hyps in the future.
        let tprf ← withLocalDeclD `h c fun hc => do
          -- let subst := subst.push hc -- hc does not occur in the term
          let wpt := mkApp5 (mkConst ``WP.wp us) m ps instWP α th
          let tprf ← onApply { goal with target := mkAppN (mkConst ``PredTrans.apply) (args.set! 2 wpt) } subst
          mkLambdaFVars #[hc] tprf
        let eprf ← withLocalDeclD `h (mkApp (mkConst ``Not) c) fun hnc => do
          -- let subst := subst.push hnc -- hnc does not occur in the term
          let wpe := mkApp5 (mkConst ``WP.wp us) m ps instWP α el
          let eprf ← onApply { goal with target := mkAppN (mkConst ``PredTrans.apply) (args.set! 2 wpe) } subst
          mkLambdaFVars #[hnc] eprf
        let prf := mkApp5 (mkConst ``split_ite us) α m ps goal.hyps Q
        let prf := mkApp5 prf c instDec instWP th el
        let prf := mkApp2 prf tprf eprf
        -- logInfo m!"prf: {prf}"
        --check (prf.instantiateRev subst)
        return prf
      | Pure.pure _m _ _α a =>
        burnOne
        let some (instMon, instWPMon) := monad? | failure
        return ← withNonTrivialLetDecl `a α a fun a leave => do
        let subst := subst.push a -- TODO: Does the wrong thing when we don't bind a
        let goal := { goal with target := mkAppN (mkApp (mkProj ``Prod 0 Q) a) args[4:] }
        let prf₁ ← discharge goal.toExpr subst
        let prf₂ := mkApp7 (mkConst ``Specs.pure) m ps instMon instWPMon α a Q
        let prf ← mkAppM ``SPred.entails.trans #[prf₁, prf₂]
        check prf
        return ← leave prf
      | Bind.bind _m _ α' _ x k =>
        burnOne
        let some (instMon, instWPMon) := monad? | failure
        let Qty := mkApp2 (mkConst ``PostCond) α ps
        return ← withNonTrivialLetDecl `Q Qty Q fun Q leaveQ => do
        let subst := subst.push Q
        let name := match k with | .lam n .. => n | _ => `a
        let kapplyQ ← withLocalDeclD name α' fun a => do
          let wpk := mkApp5 (mkConst ``WP.wp us) m ps instWP α (k.betaRev #[a])
          mkForallFVars #[a] (← onApply { goal with target := mkAppN (mkConst ``PredTrans.apply) (args.set! 2 wpk |>.set! 3 Q) } subst)
        logInfo m!"kapplyQ: {kapplyQ}, type: {← inferType kapplyQ}"
        let Q' ← mkAppM ``Prod.mk #[← inferType kapplyQ, mkProj ``Prod 1 Q]
        logInfo m!"Q': {Q'}"
        let wpx := mkApp5 (mkConst ``WP.wp us) m ps instWP α x
        let prf ← onApply { goal with target := mkAppN (mkConst ``PredTrans.apply) (args.set! 2 wpx |>.set! 3 Q') } subst
        let prf := mkApp (mkApp10 (mkConst ``Specs.bind_pre) m ps α' α instMon instWPMon x k goal.hyps Q) prf
        leaveQ prf
      | _ => return ← discharge goal.toExpr subst
      -- Split match-expressions
      --if let some info := isMatcherAppCore? (← getEnv) e then
      --  let candidate ← id do
      --    let args := e.getAppArgs
      --    logInfo "e: {e}, args: {args}"
      --    for i in [info.getFirstDiscrPos : info.getFirstDiscrPos + info.numDiscrs] do
      --      if args[i]!.hasLooseBVars then
      --        return false
      --    return true
      --  if candidate then
      --    -- We could be even more deliberate here and use the `lifter` lemmas
      --    -- for the match statements instead of the `split` tactic.
      --    -- For now using `splitMatch` works fine.
      --    -- return ← Split.splitMatch goal e
      --    return (fuel, ← discharge goal subst)
    | _ => return ← discharge goal.toExpr subst

end VC

elab "mvcgen_step" n:(num)? : tactic => do
  let n := n.map (·.raw.toNat) |>.getD 1
  let (mvar, goal) ← mStart (← getMainGoal)
  mvar.withContext do
  let goals ← IO.mkRef []
  mvar.assign (← VC.step (fuel := .limited n) goal #[] fun hyp subst => do
    let m ← mkFreshExprSyntheticOpaqueMVar (hyp.instantiate subst)
    goals.modify (m.mvarId! :: ·)
    return m)
  replaceMainGoal (← goals.get)

elab "mvcgen" : tactic => do
  let (mvar, goal) ← mStart (← getMainGoal)
  mvar.withContext do
  let goals ← IO.mkRef []
  mvar.assign (← VC.step (fuel := .unlimited) goal #[] fun hyp subst => do
    let m ← mkFreshExprSyntheticOpaqueMVar (hyp.instantiate subst)
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

theorem fib_triple_vc : ⦃⌜True⌝⦄ fib_impl n ⦃⇓ r => r = fib_spec n⦄ := by
  unfold fib_impl
  mvcgen_step 5
--  dsimp
--  mintro _
--  if h : n = 0 then simp [h] else
--  simp only [h]
--  mwp
--  mspec Specs.forIn_list (⇓ (⟨a, b⟩, xs) => a = fib_spec xs.rpref.length ∧ b = fib_spec (xs.rpref.length + 1)) ?step
--  case step => dsimp; intros; mintro _; mwp; simp_all
--  simp_all [Nat.sub_one_add_one]

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
