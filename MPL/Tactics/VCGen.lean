/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
import MPL.SPred.ProofMode.Tactics.Basic
import MPL.WP
import MPL.WPMonad
import MPL.WPMonadLift
import MPL.WPMonadFunctor
import MPL.WPMonadExceptOf

import MPL.SPred.ProofMode.Tactics.Intro
import MPL.SPred.ProofMode.Tactics.Cases
import MPL.SPred.ProofMode.Tactics.Specialize
import MPL.Tactics.Utils
import MPL.Triple
import MPL.Tactics.LetElim
import MPL.Tactics.Spec

/-!
# Tactic `mvcgen`
-/

namespace MPL.Tactics
open Lean Parser Elab Tactic Meta
open MPL SPred.ProofMode Tactics

initialize registerTraceClass `mpl.tactics.vcgen

namespace MPL.SPred.ProofMode.Tactics.VC

inductive Fuel where
| limited (n : Nat)
| unlimited
deriving DecidableEq

structure Config where
  /--
  If true, do not substitute away let-declarations that are used at most once.
  -/
  noLetElim : Bool := false

declare_config_elab elabConfig Config

structure Context where
  config : Config
  specThms : SpecTheorems
  simpCtx : Simp.Context
  simprocs : Simp.SimprocsArray

structure State where
  fuel : Fuel := .unlimited
  simpState : Simp.State := {}
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

def liftSimpM (x : SimpM α) : VCGenM α := do
  let ctx ← read
  let s ← get
  let mref := (Simp.mkDefaultMethodsCore ctx.simprocs).toMethodsRef
  let (a, simpState) ← x mref ctx.simpCtx |>.run s.simpState
  set { s with simpState }
  return a

instance : MonadLift SimpM VCGenM where
  monadLift x := liftSimpM x

syntax (name := mvcgen_step) "mvcgen_step" optConfig
 (num)? (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")? : tactic

syntax (name := mvcgen_no_trivial) "mvcgen_no_trivial" optConfig
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")? : tactic

syntax (name := mvcgen) "mvcgen" optConfig
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")? : tactic

private def mkSpecContext (optConfig : Syntax) (lemmas : Syntax) (ignoreStarArg := false) : TacticM Context := do
  let config ← elabConfig optConfig
  let mut specThms ← getSpecTheorems
  let mut simpStuff := #[]
  let mut starArg := false
  for arg in lemmas[1].getSepArgs do
    if arg.getKind == ``simpErase then
      try
        -- Try and build SpecTheorems for the lemma to erase to see if it's
        -- meant to be interpreted by SpecTheorems. Otherwise fall back to SimpTheorems.
        let specThm ←
          if let some fvar ← Term.isLocalIdent? arg[1] then
            mkSpecTheoremFromLocal fvar.fvarId!
          else
            let id := arg[1]
            if let .ok declName ← observing (realizeGlobalConstNoOverloadWithInfo id) then
              mkSpecTheoremFromConst declName
            else
              withRef id <| throwUnknownConstant id.getId.eraseMacroScopes
        specThms := specThms.eraseCore specThm.proof
      catch _ =>
        simpStuff := simpStuff.push ⟨arg⟩ -- simp tracks its own erase stuff
    else if arg.getKind == ``simpLemma then
      unless arg[0].isNone && arg[1].isNone do
        -- When there is ←, →, ↑ or ↓ then this is for simp
        simpStuff := simpStuff.push ⟨arg⟩
        continue
      let term := arg[2]
      match ← Term.resolveId? term (withInfo := true) <|> Term.elabCDotFunctionAlias? ⟨term⟩ with
      | some (.const declName _) =>
        let info ← getConstInfo declName
        try
          let thm ← mkSpecTheoremFromConst declName
          specThms := addSpecTheoremEntry specThms thm
        catch _ =>
          simpStuff := simpStuff.push ⟨arg⟩
      | some (.fvar fvar) =>
        let decl ← getFVarLocalDecl (.fvar fvar)
        try
          let thm ← mkSpecTheoremFromLocal fvar
          specThms := addSpecTheoremEntry specThms thm
        catch _ =>
          simpStuff := simpStuff.push ⟨arg⟩
      | _ => withRef term <| throwError "Could not resolve {repr term}"
    else if arg.getKind == ``simpStar then
      starArg := true
      simpStuff := simpStuff.push ⟨arg⟩
    else
      throwUnsupportedSyntax
  -- Build a mock simp call to build a simp context that corresponds to `simp [simpStuff]`
  let stx ← `(tactic| simp +unfoldPartialApp [$(Syntax.TSepArray.ofElems simpStuff),*])
  -- logInfo s!"{stx}"
  let res ← mkSimpContext stx.raw
    (eraseLocal := false)
    (simpTheorems := getSpecSimpTheorems)
    (ignoreStarArg := ignoreStarArg)
  -- logInfo m!"{res.ctx.simpTheorems.map (·.toUnfold.toList)}"
  if starArg && !ignoreStarArg then
    let fvars ← getPropHyps
    for fvar in fvars do
      unless specThms.isErased (.local fvar) do
        try
          let thm ← mkSpecTheoremFromLocal fvar
          specThms := addSpecTheoremEntry specThms thm
        catch _ => continue
  return { config, specThms, simpCtx := res.ctx, simprocs := res.simprocs }

def isDuplicable (e : Expr) : Bool := match e with
  | .bvar .. => true
  | .mvar .. => true
  | .fvar .. => true
  | .const .. => true
  | .lit .. => true
  | .sort .. => true
  | .mdata _ e => isDuplicable e
  | .proj _ _ e => isDuplicable e
  | .lam .. => false
  | .forallE .. => false
  | .letE .. => false
  | .app .. => e.isAppOf ``OfNat.ofNat

def withSharing (name : Name) (type : Expr) (val : Expr) (k : Expr → (Expr → VCGenM Expr) → VCGenM α) (kind : LocalDeclKind := .default) : VCGenM α :=
  if isDuplicable val then
    k val pure
  else
    withLetDecl name type val (kind := kind) fun fv => do
      k fv (liftM <| mkForallFVars #[fv] ·)

theorem rewrite_program [WP m ps] {prog₁ prog₂ : m α}
  (heq : prog₁ = prog₂) (hprf : ⦃P⦄ prog₂ ⦃Q⦄) :
  ⦃P⦄ prog₁ ⦃Q⦄ := heq ▸ hprf

partial def step (ctx : Context) (fuel : Fuel) (goal : MGoal) (name : Name) : MetaM (Expr × Array MVarId) := do
  withReducible do
  let (res, state) ← StateRefT'.run (ReaderT.run (onGoal goal name) ctx) { fuel }
  return (res, state.vcs)
where
  onFail (goal : MGoal) (name : Name) : VCGenM Expr := do
    -- logInfo m!"fail {goal.toExpr}"
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
      -- trace[mpl.tactics.vcgen] "assignMVars {← mvar.getTag}, assigned: {← mvar.isAssigned}"
      if ← mvar.isAssigned then continue
      -- I used to filter for `isProp` here and add any non-Props directly as subgoals,
      -- but then we would get spurious instantiations of non-synthetic goals such as loop
      -- invariants.
      mvar.assign (← mvar.withContext <| tryGoal (← mvar.getType) (← mvar.getTag))

  onGoal goal name : VCGenM Expr := do
    let T := goal.target
    let T := (← reduceProjBeta? T).getD T -- very slight simplification
    -- logInfo m!"target: {T}"
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
    let Q := args[3]!
    match_expr ← instantiateMVarsIfMVarApp trans with
    | wp@WP.wp m ps instWP α e =>
      let e ← instantiateMVarsIfMVarApp e
      let e := e.headBeta
      trace[mpl.tactics.vcgen] "Target: {e}"
      let goalWithNewProg e' :=
        let wp' := mkApp5 wp m ps instWP α e'
        let args' := args.set! 2 wp'
        { goal with target := mkAppN (mkConst ``PredTrans.apply) args' }

      -- lambda-expressions
      if e.getAppFn'.isLambda && false then
        -- We are likely in the implementation of a StateT function; do `mintro ∀s`
        return ← onLambda goal name
      -- let-expressions
      if let .letE x ty val body _nonDep := e.getAppFn' then
        burnOne
        return ← withSharing x ty val fun fv leave => do
        let e' := ((body.instantiate1 fv).betaRev e.getAppRevArgs)
        leave (← onWPApp (goalWithNewProg e') name)
      -- match-expressions
      if let .some info := isMatcherAppCore? (← getEnv) e then
        -- Bring into simp NF
        let res? ← Simp.simpMatchDiscrs? info e
        let e ← -- returns/continues only if old e is defeq to new e
          if let .some res := res? then
            burnOne
            if let .some heq := res.proof? then
              let prf ← onWPApp (goalWithNewProg res.expr) name
              let prf := mkApp10 (mkConst ``rewrite_program wp.constLevels!) m ps α goal.hyps Q instWP e res.expr heq prf
              return prf
            else
              pure res.expr
          else
            pure e
        -- Try reduce the matcher
        let e ← match (← reduceMatcher? e) with
          | .reduced e' =>
          burnOne
          return ← onWPApp (goalWithNewProg e') name
          | .stuck _ => pure e
          | _ => pure e
        -- Last resort: Split match
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
        -- logInfo m!"unfold local var {f}, new WP: {wpe}"
        return ← onWPApp (goalWithNewProg e') name
      -- Unfold definitions according to reducibility and spec attributes,
      -- apply specifications
      if f.isConst then
        burnOne
        try
          let specThm ← findSpec ctx.specThms e
          trace[mpl.tactics.vcgen] "Candidate spec for {f.constName!}: {specThm.proof}"
          let (prf, specHoles) ← mSpec goal (fun _wp  => return (specThm, [])) tryGoal name
          assignMVars specHoles
          return prf
        catch ex =>
          trace[mpl.tactics.vcgen] "Failed to find spec. Trying simp. Reason: {ex.toMessageData}"
        let res ← Simp.simp e
        unless res.expr != e do return ← onFail goal name
        burnOne
        if let .some heq := res.proof? then
          trace[mpl.tactics.vcgen] "Simplified"
          let prf ← onWPApp (goalWithNewProg res.expr) name
          let prf := mkApp10 (mkConst ``rewrite_program wp.constLevels!) m ps α goal.hyps Q instWP e res.expr heq prf
          return prf
        else
          return ← onWPApp (goalWithNewProg res.expr) name
      return ← onFail goal name
    | _ => return ← onFail goal name

def genVCs (goal : MVarId) (ctx : Context) (fuel : Fuel) : TacticM (Array MVarId) := do
  let goal ← if ctx.config.noLetElim then pure goal else elimLets goal
  let (mvar, goal) ← mStartMVar goal
  mvar.withContext do
  let (prf, vcs) ← VC.step ctx (fuel := fuel) goal (← mvar.getTag)
  mvar.assign prf
  replaceMainGoal vcs.toList
  return vcs

@[tactic mvcgen_step]
def elabMVCGenStep : Tactic := fun stx => withMainContext do
  let ctx ← mkSpecContext stx[1] stx[3]
  let n := if stx[2].isNone then 1 else stx[2][0].toNat
  discard <| genVCs (← getMainGoal) ctx (fuel := .limited n)

@[tactic mvcgen_no_trivial]
def elabMVCGenNoTrivial : Tactic := fun stx => withMainContext do
  let ctx ← mkSpecContext stx[0] stx[1]
  discard <| genVCs (← getMainGoal) ctx (fuel := .unlimited)

@[tactic mvcgen]
def elabMVCGen : Tactic := fun stx => withMainContext do
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
