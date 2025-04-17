import Lean
import MPL.ProofMode.MGoal

open Lean Elab.Tactic Meta

namespace MPL.ProofMode.Tactics

def mStart (mvar : MVarId) : MetaM (MVarId × MGoal) := mvar.withContext do
  -- check if already in proof mode
  let goal ← instantiateMVars <| ← mvar.getType
  if let some mGoal := parseMGoal? goal then
    return (mvar, mGoal)

  let prop := mkSort .zero
  unless ← isProp goal do
    throwError "type mismatch\n{← mkHasTypeButIsExpectedMsg (← inferType goal) prop}"

  let listType := mkApp (mkConst ``List [.succ .zero]) (mkSort (.succ .zero))
  let σs ← mkFreshExprMVar listType
  let P ← mkFreshExprMVar (mkApp (mkConst ``SPred) σs)
  let inst ← synthInstance (mkApp3 (mkConst ``PropAsEntails) goal σs P)
  let prf := mkApp4 (mkConst ``ProofMode.start_entails) σs P goal inst

  let goal : MGoal := { σs,  hyps := emptyHyp σs, target := P }
  let subgoal /- : Quoted q(⊢ₛ $P)-/ ←
    mkFreshExprSyntheticOpaqueMVar goal.toExpr (← mvar.getTag)
  mvar.assign (mkApp prf subgoal)
  let goal := { goal with target := ← instantiateMVars goal.target }
  pure (subgoal.mvarId!, goal)

elab "mstart" : tactic => do
  let (mvar, _) ← mStart (← getMainGoal)
  replaceMainGoal [mvar]

elab "mstop" : tactic => do
  -- parse goal
  let mvar ← getMainGoal
  mvar.withContext do
  let goal ← instantiateMVars <| ← mvar.getType

  -- check if already in proof mode
  let some mGoal := parseMGoal? goal | throwError "not in proof mode"
  mvar.setType mGoal.strip
