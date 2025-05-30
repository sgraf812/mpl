/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Sebastian Graf
-/
import MPL.ProofMode.MGoal
import MPL.ProofMode.Tactics.Basic

namespace MPL.ProofMode.Tactics
open Lean Elab Tactic Meta


-- set_option pp.all true in
-- #check ⌜False⌝
private def falseProp (σs : Expr) : Expr := -- ⌜False⌝ standing in for an empty conjunction of hypotheses
  mkApp3 (mkConst ``SVal.curry) (.sort .zero) σs <| mkLambda `escape .default (mkApp (mkConst ``SVal.StateTuple) σs) (mkConst ``False)

elab "mexfalso" : tactic => do
  let mvar ← getMainGoal
  mvar.withContext do
  let g ← instantiateMVars <| ← mvar.getType
  let some goal := parseMGoal? g | throwError "not in proof mode"
  let newGoal := { goal with target := falseProp goal.σs }
  let m ← mkFreshExprSyntheticOpaqueMVar newGoal.toExpr
  let prf := mkApp4 (mkConst ``SPred.exfalso) goal.σs goal.hyps goal.target m
  mvar.assign prf
  replaceMainGoal [m.mvarId!]
