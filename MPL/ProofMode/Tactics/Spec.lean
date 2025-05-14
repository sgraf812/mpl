/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Sebastian Graf
-/
import MPL.ProofMode.Tactics.Basic
import MPL.ProofMode.Tactics.Intro
import MPL.ProofMode.Tactics.Pure
import MPL.ProofMode.Tactics.Assumption
import MPL.ProofMode.Tactics.Utils
import MPL.WP
import MPL.Specs -- important for MPL.Specs.bind

/-!
# Tactic `mspec` for applying Hoare triple specifications
-/

namespace MPL.ProofMode.Tactics
open Lean Elab Tactic Meta

initialize registerTraceClass `mpl.tactics.spec

theorem Spec.entails_total {α} {ps : PostShape} (p : α → Assertion ps) (q : PostCond α ps) :
  (∀ a, p a ⊢ₛ q.1 a) → PostCond.total p ⊢ₚ q := (PostCond.entails_total p q).mpr

theorem Spec.entails_partial {α} {ps : PostShape} (p : PostCond α ps) (q : α → Assertion ps) :
  (∀ a, p.1 a ⊢ₛ q a) → p ⊢ₚ PostCond.partial q := (PostCond.entails_partial p q).mpr

def findSpec (database : SpecTheorems) (prog : Expr) : MetaM Name := do
  unless prog.getAppFn'.isConst do throwError m!"not an application of a constant: {prog}"
  let candidates ← database.specs.getMatch prog
  let candidates := candidates.insertionSort fun s₁ s₂ => s₁.priority < s₂.priority
  let specs ← candidates.filterM fun spec => do
    let specProg := spec.prog.instantiateLevelParams spec.levelParams (← mkFreshLevelMVars spec.levelParams.length)
    let (_, _, specProg) ← forallMetaTelescope specProg
    -- logInfo m!"param: {specProg.hasLevelParam}, mvar: {specProg.hasLevelMVar}"
    let b ← withAssignableSyntheticOpaque <| isDefEq prog specProg
    -- logInfo s!"specProg: {specProg}, prog: {prog}, b: {b}"
    return b
  if specs.isEmpty then throwError m!"No specs found for {indentExpr prog}\nCandidates: {candidates.map (·.proof)}"
  -- if specs.size > 1 then throwError s!"multiple specs found for {prog}: {specs.map (·.proof)}"
  return specs[0]!.proof

def instantiateSpec (spec : Expr) (expectedTy : Expr) : MetaM (Expr × List MVarId) := do
  let specTy ← inferType spec
  trace[mpl.tactics.spec] "inferred specTy, pre instantiate telescope: {← instantiateMVars specTy}"
  let (mvs, _bis, specTy) ← forallMetaTelescope specTy -- Perhaps this could be done more efficiently without MVars?
  let spec := spec.beta mvs
  trace[mpl.tactics.spec] "inferred specTy, post instantiate telescope: {← instantiateMVars specTy}"
  -- withAssignableSyntheticOpaque below assigns the meta vars in expectedTy
  unless (← withAssignableSyntheticOpaque <| isDefEq specTy expectedTy) do
    Term.throwTypeMismatchError none expectedTy specTy spec
  trace[mpl.tactics.spec] "inferred specTy, post defeq: {← instantiateMVars specTy}"
  return (spec, mvs.toList.map (·.mvarId!))

def elabTermForSpec (stx : TSyntax `term) (expectedTy : Expr) : TacticM (Expr × List MVarId) := do
  if stx.raw.isIdent then
    match (← Term.resolveId? stx.raw (withInfo := true)) with
    | some spec => return ← instantiateSpec spec expectedTy
    | _      => pure ()
  -- It is vital that we supply an expected type below,
  -- otherwise `ps` will be uninstantiated on the first elaboration try
  -- and we do not get to elaborate `fun a b => True` as `α → Assertion ps`,
  -- even after instantiating `ps` to `.arg σ .pure` and retrying (a bug?).
  try
    elabTermWithHoles stx expectedTy `mspec (allowNaturalHoles := true)
  catch e : Exception =>
    trace[mpl.tactics.spec] "internal error. This happens for example when the head symbol of the spec is wrong. Message:\n  {e.toMessageData}"
    throw e

def elabSpec (stx? : Option (TSyntax `term)) (wp : Expr) : TacticM (Expr × List MVarId × Expr × Expr) := do
  let_expr WP.wp m ps instWP α prog := wp | throwError "target not a wp application {wp}"
  let [u] := wp.getAppFn'.constLevels! | throwError "Internal error: wrong number of levels in wp application"
  let stx ← stx?.getDM <| do return mkIdent (← findSpec (← getSpecTheorems) prog)
  trace[mpl.tactics.spec] "spec syntax: {stx}"
  let P ← mkFreshExprMVar (mkApp (mkConst ``Assertion) ps) (userName := `P)
  let Q ← mkFreshExprMVar (mkApp2 (mkConst ``PostCond) α ps) (userName := `Q)
  let expectedTy := mkApp7 (mkConst ``Triple [u]) m ps instWP α prog P Q
  trace[mpl.tactics.spec] "expected type: {← instantiateMVars expectedTy}"
  let (spec, mvarIds) ← Term.withSynthesize (elabTermForSpec stx expectedTy)
  trace[mpl.tactics.spec] "inferred spec: {← instantiateMVars spec}"
  let mvarIds ← mvarIds.filterM (not <$> ·.isAssigned)
  let P ← instantiateMVars P
  let Q ← instantiateMVars Q
  return (spec, mvarIds, P, Q)

variable {n} [Monad n] [MonadControlT MetaM n] [MonadLiftT MetaM n]

mutual
partial def dischargePostEntails (α : Expr) (ps : Expr) (Q : Expr) (Q' : Expr) (goalTag : Name) (resultName : Name) (discharge : Expr → Name → n Expr) : n Expr := do
  -- Often, Q' is fully instantiated while Q contains metavariables. Try refl
  if (← isDefEq Q Q') then
    return mkApp3 (mkConst ``PostCond.entails.refl) α ps Q'
  let Q ← whnfR Q
  let Q' ← whnfR Q'
  -- If Q (postcond of the spec) is just an fvar, we do not decompose further
  if let some _fvarId := Q.fvarId? then
    return ← discharge (mkApp4 (mkConst ``PostCond.entails) α ps Q Q') `post
  -- Otherwise decompose the conjunction
  let prf₁ ← withLocalDeclD resultName α fun a => do
    let Q1a := (← mkProj' ``Prod 0 Q).betaRev #[a]
    let Q'1a := (← mkProj' ``Prod 0 Q').betaRev #[a]
    let σs := mkApp (mkConst ``PostShape.args) ps
    let goal := MGoal.mk σs (Hyp.mk `h Q1a).toExpr Q'1a
    mkLambdaFVars #[a] (← discharge goal.toExpr (goalTag ++ `success))
  let prf₂ ← dischargeFailEntails ps (← mkProj' ``Prod 1 Q) (← mkProj' ``Prod 1 Q') (goalTag ++ `except) discharge
  mkAppM ``And.intro #[prf₁, prf₂] -- This is just a bit too painful to construct by hand

partial def dischargeFailEntails (ps : Expr) (Q : Expr) (Q' : Expr) (goalTag : Name) (discharge : Expr → Name → n Expr) : n Expr := do
  if ps.isAppOf ``PostShape.pure then
    return mkConst ``True.intro
  if ← isDefEq Q Q' then
    return mkApp2 (mkConst ``FailConds.entails.refl) ps Q
  if ← isDefEq Q (mkApp (mkConst ``FailConds.false) ps) then
    return mkApp2 (mkConst ``FailConds.entails_false) ps Q'
  if ← isDefEq Q' (mkApp (mkConst ``FailConds.true) ps) then
    return mkApp2 (mkConst ``FailConds.entails_true) ps Q
  -- the remaining cases are recursive.
  if let some (_σ, ps) := ps.app2? ``PostShape.arg then
    return ← dischargeFailEntails ps Q Q' goalTag discharge
  if let some (ε, ps) := ps.app2? ``PostShape.except then
    let Q ← whnfR Q
    let Q' ← whnfR Q'
    let prf₁ ← withLocalDeclD goalTag ε fun e => do
      let Q1e := (← mkProj' ``Prod 0 Q).betaRev #[e]
      let Q'1e := (← mkProj' ``Prod 0 Q').betaRev #[e]
      let σs := mkApp (mkConst ``PostShape.args) ps
      let goal := MGoal.mk σs (Hyp.mk `h Q1e).toExpr Q'1e
      mkLambdaFVars #[e] (← discharge goal.toExpr (goalTag ++ `handle))
    let prf₂ ← dischargeFailEntails ps (← mkProj' ``Prod 1 Q) (← mkProj' ``Prod 1 Q') (goalTag ++ `except) discharge
    return ← mkAppM ``And.intro #[prf₁, prf₂] -- This is just a bit too painful to construct by hand
  -- This case happens when decomposing with unknown `ps : PostShape`
  discharge (mkApp3 (mkConst ``FailConds.entails) ps Q Q') goalTag
end

def dischargeMGoal (goal : MGoal) (goalTag : Name) (discharge : Expr → Name → n Expr) : n Expr := do
  controlAt MetaM (fun map => do trace[mpl.tactics.spec] "dischargeMGoal: {(← reduceProj? goal.target).getD goal.target}"; map (pure ()))
  -- simply try one of the assumptions for now. Later on we might want to decompose conjunctions etc; full xsimpl
  let some prf ← liftM (m:=MetaM) goal.assumption | discharge goal.toExpr goalTag
  return prf

def mSpec (goal : MGoal) (elabSpecAtWP : Expr → n (Expr × List MVarId × Expr × Expr)) (discharge : Expr → Name → n Expr) (preTag := `pre) (resultName := `r) : n (Expr × List MVarId) := do
  -- First instantiate `fun s => ...` in the target.
  -- This is like repeated `mintro ∀s`.
  lambdaTelescope goal.target.consumeMData fun xs T => do
  let goal : MGoal :=
    { target := T,
      σs := ← dropStateList goal.σs xs.size,
      hyps := betaPreservingHypNames goal.σs goal.hyps xs }

  -- Elaborate the spec
  let mut (fn, args) := T.getAppFnArgs
  unless fn == ``PredTrans.apply do liftM (m:=MetaM) (throwError "target not a PredTrans.apply application {T}")
  let wp := args[2]!
  let_expr WP.wp _m ps _instWP α _prog := wp | do liftM (m:=MetaM) (throwError "target not a wp application {wp}")
  let Q' := args[3]!
  let excessArgs := (args.extract 4 args.size).reverse
  let (spec, specHoles, P, Q) ← controlAt MetaM fun map => map (elabSpecAtWP wp)
  let P := P.betaRev excessArgs
  let spec := spec.betaRev excessArgs

  -- first try instantiation if P or Q is schematic (i.e. an MVar app)
  let mut HPRfl := false
  let mut QQ'Rfl := false
  let P ← instantiateMVarsIfMVarApp P
  let Q ← instantiateMVarsIfMVarApp Q
  if P.getAppFn.isMVar then
    let _ ← withAssignableSyntheticOpaque <| isDefEq P goal.hyps
    HPRfl := true
  if Q.getAppFn.isMVar then
    let _ ← withAssignableSyntheticOpaque <| isDefEq Q Q'
    QQ'Rfl := true

  -- Discharge the validity proof for the spec if not rfl
  let mut prePrf : Expr → Expr := id
  if !HPRfl then
    let P ← instantiateMVarsIfMVarApp P
    -- let P := (← reduceProjBeta? P).getD P
    let HPPrf ← dischargeMGoal { goal with target := P } preTag discharge
    prePrf := mkApp6 (mkConst ``SPred.entails.trans) goal.σs goal.hyps P goal.target HPPrf

  -- Discharge the entailment on postconditions if not rfl
  let mut postPrf : Expr → Expr := id
  if !QQ'Rfl then
    let wpApplyQ  := mkApp4 (mkConst ``PredTrans.apply) ps α wp Q  -- wp⟦x⟧.apply Q; that is, T without excess args
    let wpApplyQ' := mkApp4 (mkConst ``PredTrans.apply) ps α wp Q' -- wp⟦x⟧.apply Q'
    let QQ' ← dischargePostEntails α ps Q Q' `post resultName discharge
    let QQ'mono := mkApp6 (mkConst ``PredTrans.mono) ps α wp Q Q' QQ'
    postPrf := fun h =>
      mkApp6 (mkConst ``SPred.entails.trans) goal.σs P (wpApplyQ.betaRev excessArgs) (wpApplyQ'.betaRev excessArgs)
        h (QQ'mono.betaRev excessArgs)

  -- finally build the proof; HPPrf.trans (spec.trans QQ'mono)
  let prf := prePrf (postPrf spec)
  let prf ← mkLambdaFVars xs prf -- Close over the `mintro ∀s`'d vars
  return (prf, specHoles)

private def addMVar (mvars : IO.Ref (List MVarId)) (goal : Expr) (name : Name) : MetaM Expr := do
  let m ← mkFreshExprSyntheticOpaqueMVar goal (tag := name)
  mvars.modify (m.mvarId! :: ·)
  return m

syntax "mspec_no_bind" (ppSpace colGt term)? : tactic

elab "mspec_no_bind" spec:optional(term) : tactic => withMainContext do
  let (mvar, goal) ← mStartMVar (← getMainGoal)
  let goals ← IO.mkRef []
  let (prf, specHoles) ← mSpec goal (elabSpec spec) (fun goal name => liftM (m:=MetaM) (addMVar goals goal name))
  check prf
  mvar.assign prf
  let goals ← goals.get
  if let [mvar'] := goals then mvar'.setTag (← mvar.getTag)
  replaceMainGoal (goals ++ specHoles)

syntax "mspec_no_simp" (ppSpace colGt term)? : tactic

/--
  `mspec` is an `apply`-like tactic that applies a Hoare triple specification to the target of the
  stateful goal.

  Given a stateful goal `H ⊢ₛ wp⟦prog⟧.apply Q'`, `mspec foo_spec` will instantiate
  `foo_spec : ... → ⦃P⦄ foo ⦃Q⦄`, match `foo` against `prog` and produce subgoals for
  `?pre : H ⊢ₛ P` and `?post : Q ⊢ₚ Q'`.

  * If `prog = x >>= f`, then `mspec Specs.bind` is tried first so that `foo` is matched against `x`
    instead. Tactic `mspec_no_bind` does not attempt to do this decomposition.
  * If `?pre` or `?post` follow by `.rfl`, then they are discharged automatically.
  * `?post` is automatically simplified into constituent `⊢ₛ` entailments on
    success and failure continuations.
  * `?pre` and `?post.*` goals introduce their stateful hypothesis as `h` and introduce result
    binders as `r`.
  * Any uninstantiated MVar from instantiating `foo_spec` becomes a new subgoal.

  Additionally,
  * `mspec` without argument will try and look up a spec for `x` registered with `@[spec]`.
  * `mspec (foo_spec blah ?bleh)` will elaborate its argument as a term with expected type
    `⦃?P⦄ x ⦃?Q⦄` and introduce `?bleh` as a subgoal.
    This is useful to pass an invariant to e.g., `Specs.forIn_list` and leave the inductive step
    as a hole.
-/
syntax "mspec" (ppSpace colGt term)? : tactic
macro_rules
  | `(tactic| mspec_no_simp $[$spec]?) => `(tactic| ((try with_reducible mspec_no_bind MPL.Specs.bind); mspec_no_bind $[$spec]?))
  | `(tactic| mspec $[$spec]?)         => `(tactic| mspec_no_simp $[$spec]?; all_goals ((try simp only [SPred.true_intro_simp, SPred.true_intro_simp_nil, SVal.curry_cons, SVal.uncurry_cons, SVal.getThe_here, SVal.getThe_there]); (try mpure_intro; trivial)))

example (Q : SPred []) : Q ⊢ₛ k%2 = k%2 := by simp only [SPred.true_intro_simp_nil]
example (Q : SPred []) : Q ⊢ₛ ⌜k%2 = k%2⌝ := by simp only [SPred.true_intro_simp]

/-
abbrev M := StateT Nat (StateT Char (StateT Bool (StateT String Idd)))
example : ⦃isValid⦄ pure (f := M) (a + b + c) ⦃⇓r => ⌜r > 100⌝ ∧ isValid⦄ := by
  mintro h
  -- set_option trace.Meta.whnf true in
  set_option trace.mpl true in
  mspec
-/
