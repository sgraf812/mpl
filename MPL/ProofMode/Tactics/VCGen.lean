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
import MPL.Util.LetElim

/-!
# Tactic `mvcgen`
-/

namespace MPL.ProofMode.Tactics
open Lean Parser Elab Tactic Meta
open MPL Util

initialize registerTraceClass `mpl.tactics.vcgen

namespace MPL.ProofMode.Tactics.VC

inductive Fuel where
| limited (n : Nat)
| unlimited
deriving DecidableEq

structure Config where

declare_config_elab elabConfig Config

structure Context where
  specThms : SpecTheorems

structure State where
  fuel : Fuel := .unlimited
  /--
  The verification conditions that have been generated so far.
  Includes `Type`-valued goals arising from instantiation of specifications.
  -/
  vcs : Array MVarId := #[]

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

def emitVC (subGoal : Expr) (name : Name) : VCGenM Expr := do
  let m ← liftM <| mkFreshExprSyntheticOpaqueMVar subGoal (tag := name)
  modify fun s => { s with vcs := s.vcs.push m.mvarId! }
  return m

def addSubGoalAsVC (goal : MVarId) : VCGenM PUnit := do
  modify fun s => { s with vcs := s.vcs.push goal }

/-- A spec lemma specification is a term that instantiates to a hoare triple spec. -/
syntax specLemma := term
/-- An erasure specification `-thm` says to remove `thm` from the spec set -/
syntax specErase := "-" ident

syntax (name := mvcgen_step) "mvcgen_step" optConfig
 (num)? (" [" withoutPosition((specErase <|> specLemma),*,?) "]")? : tactic

syntax (name := mvcgen_no_trivial) "mvcgen_no_trivial" optConfig
  (" [" withoutPosition((specErase <|> specLemma),*,?) "]")? : tactic

syntax (name := mvcgen) "mvcgen" optConfig
  (" [" withoutPosition((specErase <|> specLemma),*,?) "]")? : tactic

private def mkSpecContext (optConfig : Syntax) (lemmas : Syntax) : TacticM Context := do
  let _config ← elabConfig optConfig
  let mut specThms ← getSpecTheorems
  if lemmas.isNone then return { specThms }
  for arg in lemmas[1].getSepArgs do
    if arg.getKind == ``specErase then
      if let some fvar ← Term.isLocalIdent? arg[1] then
        specThms := specThms.eraseCore (.local fvar.fvarId!)
      else
        let id := arg[1]
        if let .ok declName ← observing (realizeGlobalConstNoOverloadWithInfo id) then
          specThms := specThms.eraseCore (.global declName)
        else
          withRef id <| throwUnknownConstant id.getId.eraseMacroScopes
    else if arg.getKind == ``specLemma then
      let term := arg[0]
      match ← Term.resolveId? term (withInfo := true) <|> Term.elabCDotFunctionAlias? ⟨term⟩ with
      | some (.const declName _) =>
        let info ← getConstInfo declName
        if (← isProp info.type) then
          let thm ← mkSpecTheoremFromConst declName
          specThms := addSpecTheoremEntry specThms thm
        else if info.hasValue then
          specThms := specThms.addDeclToUnfoldCore declName
        else
          throwError "invalid argument, constant is not a theorem or definition"
      | some (.fvar fvar) =>
        let decl ← getFVarLocalDecl (.fvar fvar)
        if (← isProp decl.type) then
          let thm ← mkSpecTheoremFromLocal fvar
          specThms := addSpecTheoremEntry specThms thm
        else if decl.hasValue then
          specThms := specThms.addLetDeclToUnfold fvar
        else
          throwError "invalid argument, variable is not a proposition or let-declaration"
      | _ => throwError "Could not resolve {term}"
    else
      throwUnsupportedSyntax
  return { specThms }

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

partial def step (ctx : Context) (fuel : Fuel) (goal : MGoal) (name : Name) : MetaM (Expr × Array MVarId) := do
  withReducible do
  let (res, state) ← StateRefT'.run (ReaderT.run (onGoal goal name) ctx) { fuel }
  return (res, state.vcs)
where
  onFail (goal : MGoal) (name : Name) : VCGenM Expr := do
    emitVC goal.toExpr name

  tryGoal (goal : Expr) (name : Name) : VCGenM Expr := do
    forallTelescope goal fun xs body => do
      let res ← try mStart body catch _ =>
        return ← mkLambdaFVars xs (← emitVC goal name)
      let mut prf ← onGoal res.goal name
      -- logInfo m!"tryGoal: {res.goal.toExpr}"
      -- res.goal.checkProof prf
      if let some proof := res.proof? then
        prf := mkApp proof prf
      mkLambdaFVars xs prf

  assignMVars (mvars : List MVarId) : VCGenM PUnit := do
    for mvar in mvars do
      if ← mvar.isAssigned then continue
      -- I used to filter for `isProp` here and add any non-Props directly as subgoals,
      -- but then we would get spurious instantiations of non-synthetic goals such as loop
      -- invariants.
      mvar.assign (← mvar.withContext <| tryGoal (← mvar.getType) (← mvar.getTag))

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
    -- logInfo m!"trans: {trans}"
    --let Q := args[3]!
    match_expr ← instantiateMVarsIfMVarApp trans with
    | hd@WP.wp m ps instWP α e =>
      let us := hd.constLevels!
      let e ← instantiateMVarsIfMVarApp e
      let goalWithNewExpr e' :=
        let wp' := mkApp5 (mkConst ``WP.wp us) m ps instWP α e'
        let args' := args.set! 2 wp'
        { goal with target := mkAppN (mkConst ``PredTrans.apply) args' }

      if let .letE x ty val body _nonDep := e.getAppFn' then
        burnOne
        return ← withNonTrivialLetDecl x ty val fun fv leave => do
        let e' := ((body.instantiate1 fv).betaRev e.getAppRevArgs)
        leave (← onWPApp (goalWithNewExpr e') name)
      -- Reduce match-expressions
      let e ← match (← reduceMatcher? e) with
        | .reduced e' =>
        burnOne
        return ← onWPApp (goalWithNewExpr e') name
        | .stuck _e' => pure e -- NB: Do not expose the recursor in e'; split instead.
        | _ => pure e
      -- Split match-expressions
      if isMatcherAppCore (← getEnv) e then
        -- logInfo m!"split match {e}"
        burnOne
        let mvar ← mkFreshExprSyntheticOpaqueMVar goal.toExpr (tag := name)
        let mvars ← Split.splitMatch mvar.mvarId! e
        assignMVars mvars
        return mvar
      -- Unfold local bindings (TODO don't do this unconditionally)
      let f := e.getAppFn'
      if let some (some val) ← f.fvarId?.mapM (·.getValue?) then
        burnOne
        let e' := val.betaRev e.getAppRevArgs
        let wpe := mkApp5 (mkConst ``WP.wp us) m ps instWP α e'
        -- logInfo m!"unfold local var {f}, new WP: {wpe}"
        return ← onWPApp { goal with target := mkAppN (mkConst ``PredTrans.apply) (args.set! 2 wpe) } name
      -- Unfold definitions according to reducibility and spec attributes,
      -- apply specifications
      if f.isConst then
        burnOne
        let declName := f.constName!
        -- logInfo m!"const: {declName}"
        let minfo ← getUnfoldableConst? declName
        if minfo.isSome || ctx.specThms.isDeclToUnfold declName then
          unless ctx.specThms.erased.contains (.global declName) do
          -- ignore transparencey because `getUnfoldableConst?` already checks for it,
          -- and transparency should not override a user supplied decl to unfold.
          if let some e' ← Meta.unfoldDefinition? e (ignoreTransparency := true) then
            return ← onWPApp (goalWithNewExpr e') name
          -- NB: If f.constName! is erased or we could not unfold, fall through to onFail
        else
          -- logInfo m!"try spec: {declName}"
          let (prf, specHoles) ← mSpec goal (liftM ∘ findAndElabSpec ctx.specThms) tryGoal (preTag := name)
          assignMVars specHoles
          return prf
      return ← onFail goal name
    | _ => return ← onFail goal name

def genVCs (goal : MVarId) (ctx : Context) (fuel : Fuel) : TacticM (Array MVarId) := do
  let goal ← elimLets goal
  let (mvar, goal) ← mStartMVar goal
  mvar.withContext do
  let (prf, vcs) ← VC.step ctx (fuel := fuel) goal (← mvar.getTag)
  mvar.assign prf
  replaceMainGoal vcs.toList
  return vcs

@[tactic mvcgen_step]
def elabMVCGenStep : Tactic := fun stx => do
  let ctx ← mkSpecContext stx[1] stx[3]
  let n := if stx[2].isNone then 1 else stx[2][0].toNat
  discard <| genVCs (← getMainGoal) ctx (fuel := .limited n)

@[tactic mvcgen_no_trivial]
def elabMVCGenNoTrivial : Tactic := fun stx => do
  let ctx ← mkSpecContext stx[0] stx[1]
  discard <| genVCs (← getMainGoal) ctx (fuel := .unlimited)

@[tactic mvcgen]
def elabMVCGen : Tactic := fun stx => do
  -- I would like to define this simply as a macro
  -- `(tactic| mvcgen_no_trivial $c $lemmas <;> try (guard_target =~ (⌜True⌝ ⊢ₛ _); mpure_intro; trivial))
  -- but optConfig is not a leading_parser, and neither is the syntax for `lemmas`
  let ctx ← mkSpecContext stx[1] stx[2]
  let vcs ← genVCs (← getMainGoal) ctx (fuel := .unlimited)
  let tac ← `(tactic| try (guard_target =~ (⌜True⌝ ⊢ₛ _); mpure_intro; trivial))
  for vc in vcs do discard <| runTactic vc tac

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
