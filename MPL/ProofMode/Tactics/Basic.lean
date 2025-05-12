/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Sebastian Graf
-/
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
  let inst ← synthInstance (mkApp3 (mkConst ``PropAsSPredTautology) goal σs P)
  let prf := mkApp4 (mkConst ``ProofMode.start_entails) σs P goal inst

  let goal : MGoal := { σs,  hyps := emptyHyp σs, target := P }
  let subgoal ←
    mkFreshExprSyntheticOpaqueMVar goal.toExpr (← mvar.getTag)
  mvar.assign (mkApp prf subgoal)
  let goal := { goal with target := ← instantiateMVars goal.target }
  pure (subgoal.mvarId!, goal)

/--
  Start the stateful proof mode of `mpl`.
  This will transform a goal of the form `H ⊢ₛ T` into `⊢ₛ H → T`
  upon which `mintro` can be used to re-introduce `H` and give it a name.
  It is often more convenient to use `mintro` directly, which will
  try `mstart` automatically if necessary.
-/
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
