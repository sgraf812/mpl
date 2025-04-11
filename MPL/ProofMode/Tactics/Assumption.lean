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
    panic! s!"assumption: hypothesis without proper metadata: {goal.hyps}"

theorem from_tautology {σs : List Type} {P T : SProp σs} (htaut : ⊢ₛ T) : P ⊢ₛ T :=
  SProp.true_intro.trans htaut

def SGoal.assumptionPure (goal : SGoal) : OptionT MetaM Expr := do
  let fvarId ← OptionT.mk (findLocalDeclWithType? (mkApp2 (mkConst ``SProp.tautological) goal.σs goal.target))
  return mkApp4 (mkConst ``from_tautology) goal.σs goal.hyps goal.target (.fvar fvarId)

#check MVarId.assumption
elab "sassumption" : tactic => do
  let mvar ← getMainGoal
  mvar.withContext do
  let g ← instantiateMVars <| ← mvar.getType
  let some goal := parseSGoal? g | throwError "not in proof mode"

  let some proof ← liftMetaM <|
    goal.assumption <|> goal.assumptionPure
    | throwError "hypothesis not found"
  mvar.assign proof
  replaceMainGoal []
