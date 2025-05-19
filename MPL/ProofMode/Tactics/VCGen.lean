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
import MPL.ProofMode.Tactics.Utils
import MPL.Triple

/-!
# Tactic `mvcgen`
-/

namespace MPL.ProofMode.Tactics
open Lean Parser Elab Tactic Meta

initialize registerTraceClass `mpl.tactics.vcgen

namespace VC

inductive Fuel where
| limited (n : Nat)
| unlimited
deriving DecidableEq

structure Context where
  specThms : SpecTheorems

structure State where
  fuel : Fuel := .unlimited

abbrev VCGenM := ReaderT Context (StateRefT State MetaM)

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

/-- A spec lemma specification is a term that instantiates to a hoare triple spec. -/
syntax specLemma := term
/-- An erasure specification `-thm` says to remove `thm` from the spec set -/
syntax specErase := "-" ident

syntax (name := mvcgen_step) "mvcgen_step" optConfig
 (num)? (" [" withoutPosition((specErase <|> specLemma),*,?) "]")? : tactic

syntax (name := mvcgen_impl) "mvcgen_no_trivial_discharge" optConfig
  (" [" withoutPosition((specErase <|> specLemma),*,?) "]")? : tactic

/-
def mkSpecContext (optConfig : Syntax) (lemmas : Syntax) : TermElabM Context := do
  unless optConfig.isNone do throwError "mvcgen does not currently support config options"
  let mut specThms ← getSpecTheorems
  if lemmas.isNone then return { specThms }
  for arg in lemmas[1].getSepArgs do
    if arg.getKind == ``specErase then
      if let some fvar ← Term.isLocalIdent? arg[1] then
        -- We use `eraseCore` because the simp theorem for the hypothesis was not added yet
        specThms := specThms.eraseCore (.local fvar.fvarId!)
      else
        let id := arg[1]
        if let .ok declName ← observing (realizeGlobalConstNoOverloadWithInfo id) then
          -- if ctx.config.autoUnfold then
          --   thms := thms.eraseCore (.decl declName)
          -- else
          specThms ← withRef id <| specThms.eraseCore (.decl declName)
        else
          withRef id <| throwUnknownConstant name
        else if arg.getKind == ``Lean.Parser.Tactic.simpLemma then
          let post :=
            if arg[0].isNone then
              true
            else
              arg[0][0].getKind == ``Parser.Tactic.simpPost
          let inv  := !arg[1].isNone
          let term := arg[2]
          match (← resolveSimpIdTheorem? term) with
          | .expr e  =>
            let name ← mkFreshId
            thms ← addDeclToUnfoldOrTheorem ctx.indexConfig thms (.stx name arg) e post inv kind
          | .simproc declName =>
            simprocs ← simprocs.add declName post
          | .ext (some ext₁) (some ext₂) _ =>
            thmsArray := thmsArray.push (← ext₁.getTheorems)
            simprocs  := simprocs.push (← ext₂.getSimprocs)
          | .ext (some ext₁) none _ =>
            thmsArray := thmsArray.push (← ext₁.getTheorems)
          | .ext none (some ext₂) _ =>
            simprocs  := simprocs.push (← ext₂.getSimprocs)
          | .none    =>
            let name ← mkFreshId
            thms ← addSimpTheorem ctx.indexConfig thms (.stx name arg) term post inv
        else if arg.getKind == ``Lean.Parser.Tactic.simpStar then
          starArg := true
        else
          throwUnsupportedSyntax

  return
-/
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
  | .app .. => e.isAppOf ``OfNat.ofNat

def withNonTrivialLetDecl (name : Name) (type : Expr) (val : Expr) (k : Expr → (Expr → VCGenM Expr) → VCGenM α) (kind : LocalDeclKind := .default) : VCGenM α :=
  if isTrivial val then
    k val pure
  else
    withLetDecl name type val (kind := kind) fun fv => do
      k fv (liftM <| mkForallFVars #[fv] ·)

partial def step (ctx : Context) (fuel : Fuel) (goal : MGoal) (name : Name) (discharge : Expr → Name → VCGenM Expr) : MetaM Expr := do
  StateRefT'.run' (ReaderT.run (onGoal goal name) ctx) { fuel }
where
  onFail (goal : MGoal) (name : Name) : VCGenM Expr := do
    -- logInfo m!"onFail: {goal.toExpr}"
    return ← discharge goal.toExpr name

  tryGoal (goal : Expr) (name : Name) : VCGenM Expr := do
    forallTelescope goal fun xs body => do
      let res ← try mStart body catch _ =>
        return ← mkLambdaFVars xs (← discharge body name)
      let mut prf ← onGoal res.goal name
      -- logInfo m!"tryGoal: {res.goal.toExpr}"
      -- res.goal.checkProof prf
      if let some proof := res.proof? then
        prf := mkApp proof prf
      mkLambdaFVars xs prf

  onGoal goal name : VCGenM Expr := do
    let T := goal.target
    let T := (← reduceProjBeta? T).getD T -- very slight simplification
    trace[mpl.tactics.vcgen] "target: {T}"
    -- logInfo m!"onGoal: {T}"
    let goal := { goal with target := T }

    let f := T.getAppFn
    if f.isLambda then
      return ← onLambda goal name
    if f.isConstOf ``SPred.imp then
      return ← onImp goal name
    else if f.isConstOf ``PredTrans.apply then
      return ← onWPApp goal name
    onFail { goal with target := T } name

  onImp goal name : VCGenM Expr := ifOutOfFuel (onFail goal name) do
    burnOne
    (·.2) <$> mIntro goal (← `(binderIdent| _)) (fun g =>
        do return ((), ← onGoal g name))

  onLambda goal name : VCGenM Expr := ifOutOfFuel (onFail goal name) do
    burnOne
    (·.2) <$> mIntroForall goal (← `(binderIdent| _)) (fun g =>
        do return ((), ← onGoal g name))

  onWPApp goal name : VCGenM Expr := ifOutOfFuel (onFail goal name) do
    let args := goal.target.getAppArgs
    let trans := args[2]!
    --let Q := args[3]!
    -- logInfo m!"onWPApp: {trans}"
    match_expr ← instantiateMVarsIfMVarApp trans with
    | WP.wp m ps instWP α e =>
      let us := trans.getAppFn.constLevels!
      let e ← instantiateMVarsIfMVarApp e
      let f := e.getAppFn'
      if let .letE x ty val body _nonDep := f then
        burnOne
        return ← withNonTrivialLetDecl x ty val fun fv leave => do
        let e' := ((body.instantiate1 fv).betaRev e.getAppRevArgs)
        let wp' := mkApp5 (mkConst ``WP.wp us) m ps instWP α e'
        let args' := args.set! 2 wp'
        let goal := { goal with target := mkAppN (mkConst ``PredTrans.apply) args' }
        leave (← onWPApp goal name)
      if let some (some val) ← f.fvarId?.mapM (·.getValue?) then
        burnOne
        -- TODO: We do not want to unconditionally unfold let bindings in the future :(
        let e' := val.betaRev e.getAppRevArgs
        let wpe := mkApp5 (mkConst ``WP.wp us) m ps instWP α e'
        -- logInfo m!"unfold local var {f}, new WP: {wpe}"
        return ← onWPApp { goal with target := mkAppN (mkConst ``PredTrans.apply) (args.set! 2 wpe) } name
      if f.isConst then
        burnOne
        let (prf, specHoles) ← mSpec goal (liftM ∘ findAndElabSpec ctx.specThms) tryGoal (preTag := name)
        -- TODO: Better story for the generates holes
        for mvar in specHoles do
          -- logInfo m!"mvar: {← mvar.getTag} assigned: {← mvar.isAssigned}"
          if !(← mvar.isAssigned) then
            -- logInfo m!"assigning {mvar} : {← mvar.getType}"
            mvar.assign (← mvar.withContext (tryGoal (← mvar.getType) (← mvar.getTag)))
        return prf
      return ← onFail goal name
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
    | _ => return ← onFail goal name

end VC

elab "mvcgen_step" n:(num)? : tactic => do
  let n := n.map (·.raw.toNat) |>.getD 1
  let (mvar, goal) ← mStartMVar (← getMainGoal)
  mvar.withContext do
  let goals ← IO.mkRef []
  mvar.assign (← VC.step (fuel := .limited n) goal (← mvar.getTag) fun goal tag => do
    let m ← mkFreshExprSyntheticOpaqueMVar goal (tag := tag)
    goals.modify (m.mvarId! :: ·)
    return m)
  replaceMainGoal (← goals.get).reverse

elab "mvcgen_no_trivial" : tactic => do
  let (mvar, goal) ← mStartMVar (← getMainGoal)
  mvar.withContext do
  let goals ← IO.mkRef []
  mvar.assign (← VC.step (fuel := .unlimited) goal (← mvar.getTag) fun goal tag => do
    let m ← mkFreshExprSyntheticOpaqueMVar goal (tag := tag)
    goals.modify (m.mvarId! :: ·)
    return m)
  replaceMainGoal (← goals.get).reverse

macro "mvcgen" : tactic => `(tactic| mvcgen_no_trivial <;> try (guard_target =~ (⌜True⌝ ⊢ₛ _); mpure_intro; trivial))

@[tactic mvcgen_impl] def evalMVCGen : Tactic := fun stx => withMainContext do withSimpDiagnostics do
  let { ctx, simprocs, dischargeWrapper } ← mkSpecContext stx
  let stats ← dischargeWrapper.with fun discharge? =>
    simpLocation ctx simprocs discharge? (expandOptLocation stx[5])
  if tactic.simp.trace.get (← getOptions) then
    traceSimpCall stx stats.usedTheorems
  return stats.diag

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
  -- set_option trace.mpl.tactics.spec true in
  mvcgen
  case inv => exact ⇓ (⟨a, b⟩, xs) =>
    a = fib_spec xs.rpref.length ∧ b = fib_spec (xs.rpref.length + 1)
  all_goals simp_all +zetaDelta [Nat.sub_one_add_one]
