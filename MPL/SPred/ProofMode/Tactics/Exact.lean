/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Sebastian Graf
-/
import MPL.SPred.ProofMode.Tactics.Basic
import MPL.SPred.ProofMode.Focus

namespace MPL.SPred.ProofMode.Tactics
open Lean Elab Tactic Meta

theorem Exact.assumption {σs : List Type} {P P' A : SPred σs}
  (h : P ⊣⊢ₛ P' ∧ A) : P ⊢ₛ A := h.mp.trans SPred.and_elim_r

theorem Exact.from_tautology {σs : List Type} {P T : SPred σs} [PropAsSPredTautology φ T] (h : φ) : P ⊢ₛ T :=
  SPred.true_intro.trans (PropAsSPredTautology.iff.mp h)

def _root_.MPL.SPred.ProofMode.MGoal.exact (goal : MGoal) (hyp : Syntax) : OptionT MetaM Expr := do
  if goal.findHyp? hyp.getId |>.isNone then failure
  let focusRes ← goal.focusHypWithInfo ⟨hyp⟩
  OptionT.mk do
  let proof := mkApp5 (mkConst ``Exact.assumption) goal.σs goal.hyps focusRes.restHyps goal.target focusRes.proof
  unless ← isDefEq focusRes.focusHyp goal.target do
    throwError "mexact tactic failed, hypothesis {hyp} is not definitionally equal to {goal.target}"
  return proof

def _root_.MPL.SPred.ProofMode.MGoal.exactPure (goal : MGoal) (hyp : Syntax) : TacticM Expr := do
  let φ ← mkFreshExprMVar (mkSort .zero)
  let h ← elabTermEnsuringType hyp φ
  let P ← mkFreshExprMVar (mkApp (mkConst ``SPred) goal.σs)
  let some inst ← synthInstance? (mkApp3 (mkConst ``PropAsSPredTautology) φ goal.σs P)
    | throwError "mexact tactic failed, {hyp} is not an SPred tautology"
  return mkApp6 (mkConst ``Exact.from_tautology) φ goal.σs goal.hyps goal.target inst h

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
