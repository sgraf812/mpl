import MPL.ProofMode.MGoal

namespace MPL.ProofMode.Tactics

open Lean Elab Tactic Meta

def mExistsCore (mvar : MVarId) : MetaM (MVarId × MVarId) := do
  let g ← instantiateMVars <| ← mvar.getType
  let some goal := parseMGoal? g | throwError "not in proof mode"

  let mkApp3 (.const ``SPred.and []) σs L R := goal.target | throwError "target is not SPred.and"

  let leftGoal ← mkFreshExprSyntheticOpaqueMVar {goal with target := L}.toExpr
  let rightGoal ← mkFreshExprSyntheticOpaqueMVar {goal with target := R}.toExpr
  mvar.assign (mkApp6 (mkConst ``SPred.and_intro) σs goal.hyps L R leftGoal rightGoal)
  return (leftGoal.mvarId!, rightGoal.mvarId!)

elab "mexists" : tactic => do
  let mvar ← getMainGoal
  mvar.withContext do
  let (leftGoal, rightGoal) ← mExistsCore mvar
  replaceMainGoal [leftGoal, rightGoal]
