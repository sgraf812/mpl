/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
import MPL.WPMonad
import MPL.SPred.Notation
import MPL.ProofMode.MGoal

/-!
# Hoare triples

Hoare triples form the basis for compositional functional correctness proofs about monadic programs.

As usual, `triple x P Q` holds iff the precondition `P` entails the weakest precondition
`wp⟦x⟧.apply Q` of `x : m α` for the postcondition `Q`.
It is thus defined in terms of an instance `WP m ps`.
-/

namespace MPL

universe u
variable {m : Type → Type u} {ps : PostShape}

def Triple [WP m ps] {α} (x : m α) (P : Assertion ps) (Q : PostCond α ps) : Prop :=
  P ⊢ₛ wp⟦x⟧ Q

namespace Triple

notation:lead "⦃" P "⦄ " x:lead " ⦃" Q "⦄" => Triple x spred(P) spred(Q)
app_unexpand_rule Triple
  | `($_ $x $P $Q) => match Q with
    | `(⇓ $xs* => $e) => do
      `(⦃$(← SPred.Notation.unpack P)⦄ $x ⦃⇓ $xs* => $(← SPred.Notation.unpack e)⦄)
    | _ => do
      `(⦃$(← SPred.Notation.unpack P)⦄ $x ⦃$(← SPred.Notation.unpack Q)⦄)

instance [WP m ps] (x : m α) : PropAsSPredTautology (Triple x P Q) spred(P → wp⟦x⟧ Q) where
  iff := (SPred.entails_true_intro P (wp⟦x⟧ Q)).symm

theorem pure [Monad m] [WPMonad m ps] {α} {Q : PostCond α ps} (a : α) (himp : P ⊢ₛ Q.1 a) :
  ⦃P⦄ pure (f:=m) a ⦃Q⦄ := himp.trans (by simp only [pure_pure, PredTrans.pure_apply, SPred.entails.refl])

theorem bind [Monad m] [WPMonad m ps] {α β} {P : Assertion ps} {Q : α → Assertion ps} {R : PostCond β ps} (x : m α) (f : α → m β)
    (hx : ⦃P⦄ x ⦃(Q, R.2)⦄)
    (hf : ∀ b, ⦃Q b⦄ f b ⦃R⦄) :
    ⦃P⦄ (x >>= f) ⦃R⦄ := by
  apply SPred.entails.trans hx
  simp only [bind_bind]
  apply (wp x).mono _ _
  simp only [PostCond.entails, Assertion, FailConds.entails.refl, and_true]
  exact hf

theorem and [WP m ps] (x : m α) (h₁ : ⦃P₁⦄ x ⦃Q₁⦄) (h₂ : ⦃P₂⦄ x ⦃Q₂⦄) : ⦃P₁ ∧ P₂⦄ x ⦃Q₁ ∧ₚ Q₂⦄ :=
  (SPred.and_mono h₁ h₂).trans ((wp x).conjunctive Q₁ Q₂).mpr

end Triple

theorem EStateM.by_triple {α} {x : EStateM.Result ε σ α} {prog : EStateM ε σ α} (h : EStateM.run prog s = x) (P : EStateM.Result ε σ α → Prop) :
    ⦃(· = s)⦄ prog ⦃⇓ a s' => P (EStateM.Result.ok a s')⦄ → P x := by
  intro hspec
  exact EStateM.by_wp h P (hspec s rfl)
