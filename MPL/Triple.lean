import MPL.WPMonad
import MPL.SPred.Notation
import MPL.ProofMode.MGoal

namespace MPL

universe u
variable {m : Type → Type u} {ps : PredShape} [WP m ps]

def triple (x : m α) (P : PreCond ps) (Q : PostCond α ps) : Prop :=
  P ⊢ₛ wp⟦x⟧.apply Q

notation:lead "⦃" P "⦄ " x:lead " ⦃" Q "⦄" => triple x spred(P) spred(Q)
-- For some strange reason, we need the following definition if we do not depend on Mathlib:
-- syntax:lead "⦃" term "⦄ " term:lead " ⦃" term "⦄" : term
-- open Lean Elab Meta Term in
-- elab_rules : term
--   | `(⦃$P⦄ $x:term ⦃$Q⦄) => do
--     -- In a simple world, this would just be a macro expanding to
--     -- `triple $x spred($P) spred($Q)`.
--     -- However, it appears that type inference for the
--     -- postcondition Q is better when implemented manually.
--     let x ← elabTerm x none
--     let ty ← inferType x
--     tryPostponeIfMVar ty
--     let .app m α := ty | throwError "Not a type application {ty}"
--     let some u ← Level.dec <$> getLevel ty | throwError "Wrong level 0 {ty}"
--     let ps ← mkFreshExprMVar (mkConst ``PredShape)
--     let inst ← synthInstance (mkApp2 (mkConst ``WP [u]) m ps)
--     let P ← elabTerm (← `(spred($P))) (mkApp (mkConst ``PreCond) ps)
--     let Q ← elabTerm (← `(spred($Q))) (mkApp2 (mkConst ``PostCond) α ps)
--     return mkApp7 (mkConst ``triple [u]) m ps inst α x P Q
app_unexpand_rule triple
  | `($_ $x $P $Q) => match Q with
    | `(⇓ $xs* => $e) => do
      `(⦃$(← SPred.Notation.unpack P)⦄ $x ⦃⇓ $xs* => $(← SPred.Notation.unpack e)⦄)
    | _ => do
      `(⦃$(← SPred.Notation.unpack P)⦄ $x ⦃$(← SPred.Notation.unpack Q)⦄)

instance [WP m ps] (x : m α) : ProofMode.PropAsEntails (triple x P Q) spred(P → wp⟦x⟧.apply Q) where
  prop_as_entails := (SPred.entails_true_intro P (wp⟦x⟧.apply Q)).symm

theorem triple_conseq {α} (x : m α) {P P' : PreCond ps} {Q Q' : PostCond α ps}
  (hp : P.entails P' := by simp) (hq : Q'.entails Q := by simp) (h : triple x P' Q') :
  triple x P Q := by
    apply SPred.entails.trans hp
    apply SPred.entails.trans h
    apply wp⟦x⟧.mono Q' Q hq

theorem triple_pure [Monad m] [MonadMorphism m (PredTrans ps) wp] {α} {Q : PostCond α ps} (a : α) (himp : P.entails (Q.1 a)) :
  triple (pure (f:=m) a) P Q := by apply SPred.entails.trans himp (by simp only [pure_pure, PredTrans.pure_apply, SPred.entails.refl])

theorem triple_bind [Monad m] [MonadMorphism m (PredTrans ps) wp] {α β} {P : PreCond ps} {Q : α → PreCond ps} {R : PostCond β ps} (x : m α) (f : α → m β)
  (hx : triple x P (Q, R.2))
  (hf : ∀ b, triple (f b) (Q b) R) :
  triple (x >>= f) P R := by
    apply SPred.entails.trans hx
    simp only [bind_bind]
    apply wp⟦x⟧.mono _ _
    simp only [PostCond.entails, PreCond, FailConds.entails_refl, and_true]
    exact hf
