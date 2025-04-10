/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro
-/
import MPL.ProofMode.SGoal
import MPL.ProofMode.Focus

namespace MPL.ProofMode.Tactics
open Lean Elab Tactic Meta

theorem clear {σs : List Type} {P P' A Q : SProp σs}
    (hfocus : P ⊣⊢ₛ P' ∧ A) (h : P' ⊢ₛ Q) : P ⊢ₛ Q :=
    hfocus.mp.trans <| (SProp.and_mono_l h).trans SProp.and_elim_l

elab "sclear" colGt hyp:ident : tactic => do
  let mvar ← getMainGoal
  mvar.withContext do
  let g ← instantiateMVars <| ← mvar.getType
  let some goal := parseSGoal? g | throwError "not in proof mode"
  let some res := goal.focusHyp hyp.getId | throwError "unknown identifier '{hyp}'"
  let m ← mkFreshExprSyntheticOpaqueMVar (res.updateSGoal goal).toExpr

  mvar.assign (mkApp7 (mkConst ``clear) goal.σs goal.hyps
    res.restHyps res.focusHyp goal.target res.proof m)
  replaceMainGoal [m.mvarId!]
