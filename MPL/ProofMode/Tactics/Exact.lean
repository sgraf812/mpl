import MPL.ProofMode.Tactics.Basic
import MPL.ProofMode.Focus

namespace MPL.ProofMode.Tactics
open Lean Elab Tactic Meta

theorem assumption {σs : List Type} {P P' A : SProp σs}
  (h : P ⊣⊢ₛ P' ∧ A) : P ⊢ₛ A := h.mp.trans SProp.and_elim_r

elab "sexact" colGt hyp:ident : tactic => do
  let mvar ← getMainGoal
  mvar.withContext do
  let g ← instantiateMVars <| ← mvar.getType
  let some goal := parseSGoal? g | throwError "not in proof mode"
  let some focusRes := goal.focusHyp hyp.getId | throwError "hypothesis not found"
  let proof := mkApp5 (mkConst ``assumption) goal.σs goal.hyps focusRes.restHyps goal.target focusRes.proof
  unless ← isDefEq focusRes.focusHyp goal.target do
    throwError "sexact tactic failed, hypothesis is not definitionally equal to the goal"
  mvar.assign proof
  replaceMainGoal []
