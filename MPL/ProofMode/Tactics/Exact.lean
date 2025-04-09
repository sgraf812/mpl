import MPL.ProofMode.Tactics.Basic
import MPL.ProofMode.Focus

namespace MPL.ProofMode
open Lean Elab Tactic Meta

theorem assumption {σs : List Type} {P P' A : SProp σs}
  (h : P ⊣⊢ₛ P' ∧ A) : P ⊢ₛ A := h.mp.trans SProp.and_elim_r

elab "sexact" colGt hyp:ident : tactic => do
  let mvar ← getMainGoal
  mvar.withContext do
  let g ← instantiateMVars <| ← mvar.getType
  let some goal := parseSGoal? g | throwError "not in proof mode"
  let some focusRes := goal.focusHyp hyp.getId | throwError "hypothesis not found"
  let proof := mkApp5 (mkConst ``assumption) goal.σs goal.hyps focusRes.restGoal.hyps focusRes.restGoal.target focusRes.proof
  mvar.assign proof
  replaceMainGoal []
