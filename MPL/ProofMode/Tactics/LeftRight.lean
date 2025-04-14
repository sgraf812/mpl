import MPL.ProofMode.SGoal

namespace MPL.ProofMode.Tactics

open Lean Elab Tactic Meta

def sleftRightCore (right : Bool) (mvar : MVarId) : MetaM MVarId := do
  let g ← instantiateMVars <| ← mvar.getType
  let some goal := parseSGoal? g | throwError "not in proof mode"

  let mkApp3 (.const ``SPred.or []) σs L R := goal.target | throwError "target is not SPred.or"

  let (thm, keep) := if right then (``SPred.or_intro_r', R) else (``SPred.or_intro_l', L)

  let newGoal ← mkFreshExprSyntheticOpaqueMVar {goal with target := keep}.toExpr
  mvar.assign (mkApp5 (mkConst thm) σs goal.hyps L R newGoal)
  return newGoal.mvarId!

elab "sleft" : tactic => do
  let mvar ← getMainGoal
  mvar.withContext do
  let newGoal ← sleftRightCore (right := false) mvar
  replaceMainGoal [newGoal]

elab "sright" : tactic => do
  let mvar ← getMainGoal
  mvar.withContext do
  let newGoal ← sleftRightCore (right := true) mvar
  replaceMainGoal [newGoal]
