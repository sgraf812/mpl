import MPL.ProofMode.SGoal
import MPL.ProofMode.Focus
import MPL.ProofMode.Tactics.Basic

namespace MPL.ProofMode.Tactics

open Lean Elab Tactic Meta

theorem specialize_imp {P P' Q R T : SProp σs}
  (hfocus : P ⊣⊢ₛ P' ∧ Q) (hgoal : P ∧ R ⊢ₛ T) : P ∧ (Q → R) ⊢ₛ T := by
  calc sprop(P ∧ (Q → R))
    _ ⊢ₛ (P' ∧ Q) ∧ (Q → R) := SProp.and_mono_l hfocus.mp
    _ ⊢ₛ P' ∧ Q ∧ (Q → R) := SProp.and_assoc.mp
    _ ⊢ₛ P' ∧ Q ∧ R := SProp.and_mono_r (SProp.and_intro SProp.and_elim_l SProp.imp_elim_r)
    _ ⊢ₛ (P' ∧ Q) ∧ R := SProp.and_assoc.mpr
    _ ⊢ₛ P ∧ R := SProp.and_mono_l hfocus.mpr
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
  -- P ∧ (Q → R) := goal.hyps
  dbg_trace goal.hyps
  let some (σs, P, QR) := parseAnd? goal.hyps | throwError "Precondition of specializeImp violated"
  let T := goal.target
  let P':= arg.restHyps
  let hfocus := arg.proof -- P ⊣⊢ₛ P' ∧ (Q → R)
  let mkApp3 (.const ``SProp.imp []) σs Q R := QR | throwError "Expected implication {QR}"

  -- Construct new goal (hgoal from `specialize_imp`):
  let newGoal := { goal with hyps := mkAnd! σs P R }
  let newMvarId ← mkFreshExprSyntheticOpaqueMVar newGoal.toExpr
  -- Assign proof using `specialize_imp`
  mvar.assign <| mkApp8 (mkConst ``specialize_imp) σs P P' Q R T hfocus newMvarId
  return (newGoal, newMvarId.mvarId!)

theorem focus {P P' Q R : SProp σs} (hfocus : P ⊣⊢ₛ P' ∧ Q) (hnew : P' ∧ Q ⊢ₛ R) : P ⊢ₛ R :=
  hfocus.mp.trans hnew

elab "sspecialize" hyp:ident args:(colGt term:max)* : tactic => do
  let (mvar, goal) ← sstart (← getMainGoal)
  mvar.withContext do
  let some res := goal.focusHyp hyp.getId | throwError "unknown identifier '{hyp}'"

  -- Move the hypothesis down in the context, which is where the loop assumes it is:
  let newGoal := { goal with hyps := mkAnd! goal.σs res.restHyps res.focusHyp }
  let newMvar ← mkFreshExprSyntheticOpaqueMVar newGoal.toExpr
  let some _ := parseSGoal? newGoal.toExpr | throwError "Precondition of sspecialize violated"
  mvar.assign <| mkApp5 (mkConst ``focus) goal.σs goal.hyps res.restHyps res.focusHyp newMvar
  let mut goal := newGoal
  let mut mvar := newMvar.mvarId!
  dbg_trace "here {args}"

  for arg in args do
    if arg.raw.isIdent then
      if let some res := goal.focusHyp arg.raw.getId then
        (goal, mvar) ← specializeImp mvar goal res
        continue
    throwError "TODO"
--    (goal, proof) ← specializeForall goal focus arg
  let ty ← mvar.getType
  dbg_trace "{ty}"
  replaceMainGoal [mvar]
