/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
import MPL.ProofMode.Tactics.Cases
import MPL.ProofMode.Tactics.Specialize

namespace MPL.ProofMode.Tactics
open Lean Elab Tactic Meta

macro "mreplace" h₁:binderIdent " := " h₂:ident args:(colGt term:max)* : tactic =>
  `(tactic| (mspecialize $h₂ $args*; mcases $h₂ with $h₁:binderIdent))

def SDup.sdup {σs : List Type} {P Q H T : SPred σs} (hfoc : P ⊣⊢ₛ Q ∧ H) (hgoal : P ∧ H ⊢ₛ T) : P ⊢ₛ T :=
   (SPred.and_intro .rfl (hfoc.mp.trans SPred.and_elim_r)).trans hgoal

elab "mdup" h:ident " => " h₂:ident : tactic => do
  let (mvar, goal) ← mStart (← getMainGoal)
  mvar.withContext do
  let some res := goal.focusHyp h.raw.getId | throwError m!"Hypothesis {h} not found"
  let P := goal.hyps
  let Q := res.restHyps
  let H := res.focusHyp
  let H' := (Hyp.mk h₂.raw.getId H.consumeMData).toExpr
  let T := goal.target
  let newGoal := { goal with hyps := mkAnd! goal.σs P H' }
  let m ← mkFreshExprSyntheticOpaqueMVar newGoal.toExpr
  mvar.assign (mkApp7 (mkConst ``SDup.sdup) goal.σs P Q H T res.proof m)
  replaceMainGoal [m.mvarId!]

macro "mhave" h₁:ident " := " h₂:ident args:(colGt term:max)* : tactic =>
  `(tactic| (mdup $h₂ => $h₁; mspecialize $h₁ $args*))
