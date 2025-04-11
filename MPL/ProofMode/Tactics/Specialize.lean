import MPL.ProofMode.SGoal
import MPL.ProofMode.Focus
import MPL.ProofMode.Tactics.Basic

namespace MPL.ProofMode.Tactics

open Lean Elab Tactic Meta

initialize registerTraceClass `mpl.tactics.specialize

theorem specialize_imp_persistent {P P' Q R : SProp σs}
  (hrefocus : P ∧ (Q → R) ⊣⊢ₛ P' ∧ Q) : P ∧ (Q → R) ⊢ₛ P ∧ R := by
  calc sprop(P ∧ (Q → R))
    _ ⊢ₛ (P' ∧ Q) ∧ (Q → R) := SProp.and_intro hrefocus.mp SProp.and_elim_r
    _ ⊢ₛ P' ∧ Q ∧ (Q → R) := SProp.and_assoc.mp
    _ ⊢ₛ P' ∧ Q ∧ R := SProp.and_mono_r (SProp.and_intro SProp.and_elim_l SProp.imp_elim_r)
    _ ⊢ₛ (P' ∧ Q) ∧ R := SProp.and_assoc.mpr
    _ ⊢ₛ P ∧ R := SProp.and_mono_l (hrefocus.mpr.trans SProp.and_elim_l)

theorem specialize_imp_pure {P Q R : SProp σs}
  (h : ⊢ₛ Q) : P ∧ (Q → R) ⊢ₛ P ∧ R := by
  calc sprop(P ∧ (Q → R))
    _ ⊢ₛ P ∧ (Q ∧ (Q → R)) := SProp.and_mono_r (SProp.and_intro (SProp.true_intro.trans h) .rfl)
    _ ⊢ₛ P ∧ R := SProp.and_mono_r (SProp.mp SProp.and_elim_r SProp.and_elim_l)

theorem specialize_forall {P : SProp σs} {ψ : α → SProp σs}
  (a : α) : P ∧ (∀ x, ψ x) ⊢ₛ P ∧ ψ a := SProp.and_mono_r (SProp.forall_elim a)

def specializeImpPersistent (σs : Expr) (P : Expr) (QR : Expr) (arg : TSyntax `term) : OptionT TacticM (Expr × Expr) := do
  guard (arg.raw.isIdent)
  let some arg := focusHyp σs (mkAnd! σs P QR) arg.raw.getId | failure
  OptionT.mk do -- no OptionT failure after this point
  -- The goal is P ∧ (Q → R)
  -- arg.proof : P ∧ (Q → R) ⊣⊢ₛ P' ∧ Q
  -- we want to return (R, (proof : P ∧ (Q → R) ⊢ₛ P ∧ R))
  let some specHyp := parseHyp? QR | panic! "Precondition of specializeImpPersistent violated"
  let P' := arg.restHyps
  let Q := arg.focusHyp
  let hrefocus := arg.proof -- P ∧ (Q → R) ⊣⊢ₛ P' ∧ Q
  let mkApp3 (.const ``SProp.imp []) σs Q' R := specHyp.p | throwError "Expected implication {QR}"
  let proof := mkApp6 (mkConst ``specialize_imp_persistent) σs P P' Q R hrefocus
  -- check proof
  trace[mpl.tactics.specialize] "Persistently specialize {specHyp.p} with {Q}. New Goal: {mkAnd! σs P R}"
  unless ← isDefEq Q Q' do
    throwError "failed to specialize {specHyp.p} with {Q}"

  return ({ specHyp with p := R }.toExpr, proof)

private def tautological (Q : SProp σs) : Prop := ⊢ₛ Q

def specializeImpPure (_σs : Expr) (P : Expr) (QR : Expr) (arg : TSyntax `term) : OptionT TacticM (Expr × Expr) := do
  let some specHyp := parseHyp? QR | panic! "Precondition of specializeImpPure violated"
  let mkApp3 (.const ``SProp.imp []) σs Q R := specHyp.p | failure
  let (hQ, mvarIds) ← try
    elabTermWithHoles arg.raw (mkApp2 (mkConst ``tautological) σs Q) `specialize (allowNaturalHoles := true)
    catch _ => failure
  OptionT.mk do -- no OptionT failure after this point
  -- The goal is P ∧ (Q → R)
  -- we want to return (R, (proof : P ∧ (Q → R) ⊢ₛ P ∧ R))
  pushGoals mvarIds
  let proof := mkApp5 (mkConst ``specialize_imp_pure) σs P Q R hQ
  -- check proof
  trace[mpl.tactics.specialize] "Purely specialize {specHyp.p} with {Q}. New Goal: {mkAnd! σs P R}"
  -- logInfo m!"proof: {← inferType proof}"
  return ({ specHyp with p := R }.toExpr, proof)

def specializeForall (_σs : Expr) (P : Expr) (Ψ : Expr) (arg : TSyntax `term) : OptionT TacticM (Expr × Expr) := do
  let some specHyp := parseHyp? Ψ | panic! "Precondition of specializeForall violated"
  let mkApp3 (.const ``SProp.forall [u]) α σs αR := specHyp.p | failure
  let (a, mvarIds) ← try
    elabTermWithHoles arg.raw α `specialize (allowNaturalHoles := true)
    catch _ => failure
  OptionT.mk do -- no OptionT failure after this point
  pushGoals mvarIds
  let proof := mkApp5 (mkConst ``specialize_forall [u]) σs α P αR a
  let R := αR.beta #[a]
  -- check proof
  trace[mpl.tactics.specialize] "Instantiate {specHyp.p} with {a}. New Goal: {mkAnd! σs P R}"
  return ({ specHyp with p := R }.toExpr, proof)

theorem focus {P P' Q R : SProp σs} (hfocus : P ⊣⊢ₛ P' ∧ Q) (hnew : P' ∧ Q ⊢ₛ R) : P ⊢ₛ R :=
  hfocus.mp.trans hnew

elab "sspecialize" hyp:ident args:(colGt term:max)* : tactic => do
  let (mvar, goal) ← sstart (← getMainGoal)
  mvar.withContext do

  -- Want to prove goal P ⊢ T, where hyp occurs in P.
  -- So we
  -- 1. focus on hyp (referred to as H):  P ⊣⊢ₛ P' ∧ H. Prove P' ∧ H ⊢ₛ T
  -- 2. Produce a (transitive chain of) proofs
  --      P' ∧ H ⊢ P' ∧ H₁ ⊢ₛ P' ∧ H₂ ⊢ₛ ...
  --    One for each arg; end up with goal P' ∧ H' ⊢ₛ T
  -- 3. Recombine with mkAnd (NB: P' might be empty), compose with P' ∧ H' ⊣⊢ₛ mkAnd P' H'.
  -- 4. Make a new MVar for goal `mkAnd P' H' ⊢ T` and assign the transitive chain.
  let some specFocus := goal.focusHyp hyp.getId | throwError "unknown identifier '{hyp}'"
  let σs := goal.σs
  let P := specFocus.restHyps
  let mut H := specFocus.focusHyp
  let mut goal : SGoal := goal
  -- invariant: proof (_ : goal.toExpr) fills the mvar
  let mut proof : Expr → Expr :=
    mkApp7 (mkConst ``focus) σs goal.hyps P H goal.target specFocus.proof

  for arg in args do
    let res? ← OptionT.run
      (specializeImpPersistent σs P H arg
        <|> specializeImpPure σs P H arg
        <|> specializeForall σs P H arg)
    match res? with
    | some (H', H2H') =>
      -- logInfo m!"H: {H}, proof: {← inferType H2H'}"
      proof := fun hgoal => proof (mkApp6 (mkConst ``SProp.entails.trans) σs (mkAnd! σs P H) (mkAnd! σs P H') goal.target H2H' hgoal)
      H := H'
    | none =>
      throwError "Could not specialize {H} with {arg}"

  let newMVar ← mkFreshExprSyntheticOpaqueMVar { goal with hyps := mkAnd! σs P H }.toExpr
  mvar.assign (proof newMVar)
  replaceMainGoal [newMVar.mvarId!]
