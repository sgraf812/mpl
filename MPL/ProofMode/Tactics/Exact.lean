/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
import MPL.ProofMode.Tactics.Basic
import MPL.ProofMode.Focus

namespace MPL.ProofMode.Tactics
open Lean Elab Tactic Meta

theorem Exact.assumption {σs : List Type} {P P' A : SPred σs}
  (h : P ⊣⊢ₛ P' ∧ A) : P ⊢ₛ A := h.mp.trans SPred.and_elim_r

theorem Exact.from_tautology {σs : List Type} {P T : SPred σs} (htaut : ⊢ₛ T) : P ⊢ₛ T :=
  SPred.true_intro.trans htaut

def _root_.MPL.ProofMode.MGoal.exact (goal : MGoal) (hyp : TSyntax `term) : OptionT MetaM Expr := do
  let some focusRes := goal.focusHyp hyp.raw.getId | failure
  OptionT.mk do
  let proof := mkApp5 (mkConst ``Exact.assumption) goal.σs goal.hyps focusRes.restHyps goal.target focusRes.proof
  unless ← isDefEq focusRes.focusHyp goal.target do
    throwError "sexact tactic failed, hypothesis {hyp} is not definitionally equal to {goal.target}"
  return proof

def _root_.MPL.ProofMode.MGoal.exactPure (goal : MGoal) (hyp : TSyntax `term) : TacticM Expr := do
  let T := goal.target
  let expected := mkApp2 (mkConst ``SPred.tautological) goal.σs T
  let prf ← try
    elabTerm hyp expected
  catch _ => throwError "sexact tactic failed, {hyp} does not have type {expected}"
  return mkApp4 (mkConst ``Exact.from_tautology) goal.σs goal.hyps goal.target prf

elab "mexact" colGt hyp:term : tactic => do
  let mvar ← getMainGoal
  mvar.withContext do
  let g ← instantiateMVars <| ← mvar.getType
  let some goal := parseMGoal? g | throwError "not in proof mode"
  if let some prf ← liftMetaM (goal.exact hyp) then
    mvar.assign prf
  else
    mvar.assign (← goal.exactPure hyp)
  replaceMainGoal []
