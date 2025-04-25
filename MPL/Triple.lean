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
variable {m : Type → Type u} {ps : PostShape} [WP m ps]

def triple (x : m α) (P : PreCond ps) (Q : PostCond α ps) : Prop :=
  P ⊢ₛ wp⟦x⟧.apply Q

notation:lead "⦃" P "⦄ " x:lead " ⦃" Q "⦄" => triple x spred(P) spred(Q)
app_unexpand_rule triple
  | `($_ $x $P $Q) => match Q with
    | `(⇓ $xs* => $e) => do
      `(⦃$(← SPred.Notation.unpack P)⦄ $x ⦃⇓ $xs* => $(← SPred.Notation.unpack e)⦄)
    | _ => do
      `(⦃$(← SPred.Notation.unpack P)⦄ $x ⦃$(← SPred.Notation.unpack Q)⦄)

instance [WP m ps] (x : m α) : ProofMode.PropAsEntails (triple x P Q) spred(P → wp⟦x⟧.apply Q) where
  prop_as_entails := (SPred.entails_true_intro P (wp⟦x⟧.apply Q)).symm

theorem triple_pure [Monad m] [MonadMorphism m (PredTrans ps) wp] {α} {Q : PostCond α ps} (a : α) (himp : P.entails (Q.1 a)) :
  triple (pure (f:=m) a) P Q := himp.trans (by simp only [pure_pure, PredTrans.pure_apply, SPred.entails.refl])

theorem triple_bind [Monad m] [MonadMorphism m (PredTrans ps) wp] {α β} {P : PreCond ps} {Q : α → PreCond ps} {R : PostCond β ps} (x : m α) (f : α → m β)
  (hx : triple x P (Q, R.2))
  (hf : ∀ b, triple (f b) (Q b) R) :
  triple (x >>= f) P R := by
    apply SPred.entails.trans hx
    simp only [bind_bind]
    apply wp⟦x⟧.mono _ _
    simp only [PostCond.entails, PreCond, FailConds.entails.refl, and_true]
    exact hf
