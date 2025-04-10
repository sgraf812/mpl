/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro
-/
import MPL.ProofMode.SGoal
import MPL.ProofMode.Focus

namespace MPL.ProofMode.Tactics

open Lean Elab Tactic Meta

class IsPure {σs : List Type} (P : SProp σs) (φ : outParam Prop) where to_pure : P ⊣⊢ₛ ⌜φ⌝
instance (σs) : IsPure (σs:=σs) ⌜φ⌝ φ where to_pure := .rfl
instance (σs) : IsPure (σs:=σs) sprop(⌜φ⌝ → ⌜ψ⌝) (φ → ψ) where to_pure := SProp.pure_imp
instance (σs) : IsPure (σs:=σs) sprop(⌜φ⌝ ∧ ⌜ψ⌝) (φ ∧ ψ) where to_pure := SProp.pure_and
instance (σs) : IsPure (σs:=σs) sprop(⌜φ⌝ ∨ ⌜ψ⌝) (φ ∨ ψ) where to_pure := SProp.pure_or
instance (σs) (P : α → Prop) : IsPure (σs:=σs) sprop(∃ x, ⌜P x⌝) (∃ x, P x) where to_pure := SProp.pure_exists
instance (σs) (P : α → Prop) : IsPure (σs:=σs) sprop(∀ x, ⌜P x⌝) (∀ x, P x) where to_pure := SProp.pure_forall

theorem spure_thm {σs : List Type} {P P' Q R : SProp σs} {φ : Prop} [IsPure Q φ]
  (hfoc : P ⊣⊢ₛ P' ∧ Q) (h : φ → P' ⊢ₛ R) : P ⊢ₛ R := by
    have h₁ : P ⊣⊢ₛ P' ∧ ⌜φ⌝ := hfoc.trans (SProp.and_congr_r IsPure.to_pure)
    have h₂ : P' ∧ ⌜φ⌝ ⊢ₛ R := by
      apply SProp.pure_elim (φ:=φ)
      · exact SProp.and_elim_r
      · intro hp
        exact SProp.and_elim_l.trans (h hp)
    exact h₁.mp.trans h₂

def spureCore (mvarId : MVarId) (goal : SGoal) (res : FocusResult) (name : Name) : MetaM (FVarId × MVarId) := do
  let σs := goal.σs
  let φ ← mkFreshExprMVar (mkSort .zero)
  let inst ← synthInstance (mkApp3 (mkConst ``IsPure) σs res.focusHyp φ)
  let newGoalTy := mkForall name .default φ (res.updateSGoal goal).toExpr
  let newMVarId ← mkFreshExprSyntheticOpaqueMVar newGoalTy
  mvarId.assign <| mkApp9 (mkConst ``spure_thm) σs goal.hyps res.restHyps res.focusHyp goal.target φ inst res.proof newMVarId
  newMVarId.mvarId!.intro name

elab "spure" colGt hyp:ident : tactic => do
  let mvar ← getMainGoal
  mvar.withContext do
  let g ← instantiateMVars <| ← mvar.getType
  let some goal := parseSGoal? g | throwError "not in proof mode"
  let some res := goal.focusHyp hyp.getId | throwError "unknown identifier '{hyp}'"
  let (_fv, m) ← spureCore mvar goal res hyp.getId
  replaceMainGoal [m]

/-- A generalization of `SProp.pure_intro` exploiting `IsPure`. -/
theorem pure_intro {σs : List Type} {P Q : SProp σs} {φ : Prop} [IsPure Q φ] (hp : φ) : P ⊢ₛ Q :=
  (SProp.pure_intro hp).trans IsPure.to_pure.mpr

macro "spure_intro" : tactic => `(tactic| apply pure_intro)
