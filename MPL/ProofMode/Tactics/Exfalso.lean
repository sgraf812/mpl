import MPL.ProofMode.SGoal
import MPL.ProofMode.Tactics.Basic

namespace MPL.ProofMode.Tactics
open Lean Elab Tactic Meta


-- set_option pp.all true in
-- #check ⌜False⌝
private def falseProp (σs : Expr) : Expr := -- ⌜False⌝ standing in for an empty conjunction of hypotheses
  mkApp2 (mkConst ``SPred.idiom) σs <| mkLambda `escape .default (mkApp (mkConst ``SVal.EscapeFun) σs) (mkConst ``False)

elab "sexfalso" : tactic => do
  let mvar ← getMainGoal
  mvar.withContext do
  let g ← instantiateMVars <| ← mvar.getType
  let some goal := parseSGoal? g | throwError "not in proof mode"
  let newGoal := { goal with target := falseProp goal.σs }
  let m ← mkFreshExprSyntheticOpaqueMVar newGoal.toExpr
  let prf := mkApp4 (mkConst ``SPred.exfalso) goal.σs goal.hyps goal.target m
  mvar.assign prf
  replaceMainGoal [m.mvarId!]
