import MPL.ProofMode.Tactics.Basic
import MPL.ProofMode.Tactics.Exact
import MPL.ProofMode.Focus

namespace MPL.ProofMode.Tactics
open Lean Elab Tactic Meta

theorem Assumption.assumption_l {σs : List Type} {P Q R : SPred σs} (h : P ⊢ₛ R) : P ∧ Q ⊢ₛ R :=
  SPred.and_elim_l.trans h
theorem Assumption.assumption_r {σs : List Type} {P Q R : SPred σs} (h : Q ⊢ₛ R) : P ∧ Q ⊢ₛ R :=
  SPred.and_elim_r.trans h

partial def _root_.MPL.ProofMode.SGoal.assumption (goal : SGoal) : OptionT MetaM Expr := do
  if let some _ := parseEmptyHyp? goal.hyps then
    failure
  if let some hyp := parseHyp? goal.hyps then
    guard (← isDefEq hyp.p goal.target)
    return mkApp2 (mkConst ``SPred.entails.refl) goal.σs hyp.p
  if let some (σs, lhs, rhs) := parseAnd? goal.hyps then
    mkApp5 (mkConst ``Assumption.assumption_l) σs lhs rhs goal.target <$> assumption { goal with hyps := lhs }
    <|>
    mkApp5 (mkConst ``Assumption.assumption_r) σs lhs rhs goal.target <$> assumption { goal with hyps := rhs }
  else
    panic! s!"assumption: hypothesis without proper metadata: {goal.hyps}"

def _root_.MPL.ProofMode.SGoal.assumptionPure (goal : SGoal) : OptionT MetaM Expr := do
  let fvarId ← OptionT.mk (findLocalDeclWithType? (mkApp2 (mkConst ``SPred.tautological) goal.σs goal.target))
  return mkApp4 (mkConst ``Exact.from_tautology) goal.σs goal.hyps goal.target (.fvar fvarId)

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
