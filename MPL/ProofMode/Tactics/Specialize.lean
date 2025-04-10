import MPL.ProofMode.SGoal
import MPL.ProofMode.Focus
import MPL.ProofMode.Tactics.Basic

namespace MPL.ProofMode.Tactics

open Lean Elab Tactic Meta

theorem specialize_imp {P P' Q R T : SProp σs}
  (hrefocus : P ∧ (Q → R) ⊣⊢ₛ P' ∧ Q) (hgoal : P ∧ R ⊢ₛ T) : P ∧ (Q → R) ⊢ₛ T := by
  calc sprop(P ∧ (Q → R))
    _ ⊢ₛ (P' ∧ Q) ∧ (Q → R) := SProp.and_intro hrefocus.mp SProp.and_elim_r
    _ ⊢ₛ P' ∧ Q ∧ (Q → R) := SProp.and_assoc.mp
    _ ⊢ₛ P' ∧ Q ∧ R := SProp.and_mono_r (SProp.and_intro SProp.and_elim_l SProp.imp_elim_r)
    _ ⊢ₛ (P' ∧ Q) ∧ R := SProp.and_assoc.mpr
    _ ⊢ₛ P ∧ R := SProp.and_mono_l (hrefocus.mpr.trans SProp.and_elim_l)
    _ ⊢ₛ T := hgoal

theorem specialize_forall {P P' Q : SProp σs} {ψ : α → SProp σs}
  (hfocus : P ⊣⊢ₛ P' ∧ (∀ x, ψ x)) (a : α) (h : P' ∧ ψ a ⊢ₛ Q) : P ⊢ₛ Q := by
  calc P
    _ ⊢ₛ P' ∧ (∀ x, ψ x) := hfocus.mp
    _ ⊢ₛ P' ∧ ψ a := SProp.and_mono_r (SProp.forall_elim a)
    _ ⊢ₛ Q := h

theorem imp_trans_helper {P P₁ P₂ Q R : SProp σs}
  (h₁ : P ⊣⊢ₛ P₁ ∧ (Q → R)) (h₂ : P₁ ⊣⊢ₛ P₂ ∧ Q) : P ⊣⊢ₛ (P₂ ∧ Q) ∧ (Q → R) :=
    h₁.trans (SProp.and_congr_l h₂)

def specializeImp (mvar : MVarId) (goal : SGoal) (arg : FocusResult) : MetaM (SGoal × MVarId) := do
  -- P ∧ (Q → R) := goal.hyps, arg.proof : P ∧ (Q → R) ⊣⊢ₛ P' ∧ Q
  -- logInfo m!"goal.hyps: {goal.hyps}"
  -- logInfo m!"arg.proof : {← inferType arg.proof}"
  let some (_, P, QR) := parseAnd? goal.hyps | panic! s!"Precondition of specializeImp violated: context did not contain multiple hypotheses {goal.hyps}"
  let some hyp := parseHyp? QR | panic! "Precondition of specializeImp violated: right-most hyp not singleton"
  let T := goal.target
  let P':= arg.restHyps
  let Q' := arg.focusHyp
  let hrefocus := arg.proof -- P ∧ (Q → R) ⊣⊢ₛ P' ∧ Q
  let mkApp3 (.const ``SProp.imp []) σs Q R := hyp.p | throwError "Expected implication {QR}"
  unless ← isDefEq Q Q' do
    throwError "failed to specialize {hyp.p} with {Q'}"

  -- Construct new goal (hgoal from `specialize_imp`):
  let newGoal := { goal with hyps := mkAnd! σs P {hyp with p := R}.toExpr }
  let newMvarId ← mkFreshExprSyntheticOpaqueMVar newGoal.toExpr
  -- logInfo m!"newGoal: {← inferType newMvarId}"
  -- Assign proof using `specialize_imp`
  let proof := mkApp8 (mkConst ``specialize_imp) σs P P' Q R T hrefocus newMvarId
  check proof
  -- logInfo m!"proof: {← inferType proof}"
  mvar.assign proof
  return (newGoal, newMvarId.mvarId!)

theorem focus {P P' Q R : SProp σs} (hfocus : P ⊣⊢ₛ P' ∧ Q) (hnew : P' ∧ Q ⊢ₛ R) : P ⊢ₛ R :=
  hfocus.mp.trans hnew

elab "sspecialize" hyp:ident args:(colGt term:max)* : tactic => do
  let (mvar, goal) ← sstart (← getMainGoal)
  mvar.withContext do
  let some res := goal.focusHyp hyp.getId | throwError "unknown identifier '{hyp}'"

  -- Move the hypothesis down in the context, which is where the loop assumes it is:
  let (hyps, proof) := mkAnd goal.σs res.restHyps res.focusHyp
  let newGoal := { goal with hyps := hyps }
  let newMvar ← mkFreshExprSyntheticOpaqueMVar newGoal.toExpr
  let some _ := parseSGoal? newGoal.toExpr | throwError "Precondition of sspecialize violated"
  let proof := mkApp7 (mkConst ``focus) goal.σs goal.hyps res.restHyps res.focusHyp goal.target proof newMvar
  -- check proof
  mvar.assign proof
  let mut goal := newGoal
  let mut mvar := newMvar.mvarId!

  for arg in args do
    if arg.raw.isIdent then
      if let some res := goal.focusHyp arg.raw.getId then
        (goal, mvar) ← specializeImp mvar goal res
        continue
    throwError "TODO"
--    (goal, proof) ← specializeForall goal focus arg
  replaceMainGoal [mvar]
