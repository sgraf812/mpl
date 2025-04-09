import MPL.ProofMode.Tactics.Basic
import MPL.ProofMode.Focus

namespace MPL.ProofMode
open Lean Elab Tactic Meta

--theorem assumption {σs : List Type} {P P' A : SProp σs}
--  (h : P ⊣⊢ₛ P' ∧ A) : P ⊢ₛ A := h.mp.trans SProp.and_elim_r

theorem assumption_l {σs : List Type} {P Q R : SProp σs} (h : P ⊢ₛ R) : P ∧ Q ⊢ₛ R :=
  SProp.and_elim_l.trans h
theorem assumption_r {σs : List Type} {P Q R : SProp σs} (h : Q ⊢ₛ R) : P ∧ Q ⊢ₛ R :=
  SProp.and_elim_r.trans h

partial def SGoal.assumption (goal : SGoal) : OptionT MetaM Expr := do
  if let some _ := parseEmptyHyp? goal.hyps then
    failure
  if let some hyp := parseHyp? goal.hyps then
    guard (← isDefEq hyp.p goal.target)
    return mkApp2 (mkConst ``SProp.entails.refl) goal.σs hyp.p
  if let some (σs, lhs, rhs) := parseAnd? goal.hyps then
    mkApp5 (mkConst ``assumption_l) σs lhs rhs goal.target <$> assumption { goal with hyps := lhs }
    <|>
    mkApp5 (mkConst ``assumption_r) σs lhs rhs goal.target <$> assumption { goal with hyps := rhs }
  else
    failure

elab "sassumption" : tactic => do
  let mvar ← getMainGoal
  mvar.withContext do
  let g ← instantiateMVars <| ← mvar.getType
  let some goal := parseSGoal? g | throwError "not in proof mode"

  let some proof ← liftMetaM goal.assumption | throwError "hypothesis not found"
  mvar.assign proof
  replaceMainGoal []
