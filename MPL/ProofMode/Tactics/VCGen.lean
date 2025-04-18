import MPL.ProofMode.Tactics.Basic
import MPL.WPSimp
import MPL.WP

namespace MPL.ProofMode.Tactics
open Lean Elab Tactic Meta

elab "mvcgen" : tactic => do
  let mvar ← getMainGoal
  let some _ := parseMGoal? (← instantiateMVars <| ← mvar.getType) | throwError "vcgen: not in proof mode"
  -- Somehow, conv in ... => rfl breaks the use of `withCollectingNewGoalsFrom` in `mspec`.
  -- I won't investigate because wp_simp will be replaced anyway.
  --  let (mvars, _) ← runTactic mvar (← `(tactic| conv in SPred.entails _ _ => arg 2; tactic => wp_simp))
  let (mvars, _) ← runTactic mvar (← `(tactic| wp_simp))
  replaceMainGoal mvars
