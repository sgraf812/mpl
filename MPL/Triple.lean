import MPL.WPMonad

namespace MPL

universe u
variable {m : Type → Type u} {ps : PredShape} [WP m ps]

def triple (x : m α) (P : PreCond ps) (Q : PostCond α ps) : Prop :=
  P ⊢ₛ wp⟦x⟧.apply Q

syntax:lead "⦃" term "⦄ " term:lead " ⦃" term "⦄" : term
-- syntax:lead "⦃" term "⦄ " term:lead " ⦃⇓" ident " | " term "⦄" : term
macro_rules
  | `(⦃$P⦄ $x:term ⦃$Q⦄) => `(triple $x sprop($P) sprop($Q))
--  | `(⦃$P⦄ $x:term ⦃⇓ $v | $Q⦄) => `(triple $x sprop($P) (PostCond.total fun $v => sprop($Q)))

theorem triple_conseq {α} (x : m α) {P P' : PreCond ps} {Q Q' : PostCond α ps}
  (hp : P.entails P' := by simp) (hq : Q'.entails Q := by simp) (h : triple x P' Q') :
  triple x P Q := by
    apply SProp.entails_trans hp
    apply SProp.entails_trans h
    apply wp⟦x⟧.mono Q' Q hq

theorem triple_extract_persistent {α} {P : Prop} {P' : PreCond ps} {Q : PostCond α ps}
  (x : m α) (h : P → triple x P' Q) :
  triple (ps:=ps) x sprop(⌜P⌝ ∧ P') Q := PreCond.imp_pure_extract_l h

theorem triple_pure [Monad m] [MonadMorphism m (PredTrans ps) wp] {α} {Q : PostCond α ps} (a : α) (himp : P.entails (Q.1 a)) :
  triple (pure (f:=m) a) P Q := by apply SProp.entails_trans himp (by simp only [pure_pure, PredTrans.pure_apply, SProp.entails_refl])

theorem triple_bind [Monad m] [MonadMorphism m (PredTrans ps) wp] {α β} {P : PreCond ps} {Q : α → PreCond ps} {R : PostCond β ps} (x : m α) (f : α → m β)
  (hx : triple x P (Q, R.2))
  (hf : ∀ b, triple (f b) (Q b) R) :
  triple (x >>= f) P R := by
    apply SProp.entails_trans hx
    simp only [bind_bind]
    apply wp⟦x⟧.mono _ _
    simp only [PostCond.entails, PreCond, FailConds.entails_refl, and_true]
    exact hf

/-
theorem triple_bind2 [Monad m] [MonadMorphism m (PredTrans ps) wp] {α β} {P : PreCond ps} {R : PostCond β ps} (x : m α) (f : α → m β)
  (h : triple x P (fun a => wp⟦f a⟧.apply R, R.2)) :
  triple (x >>= f) P R := triple_bind x f h (fun _ => le_rfl)
-/
--theorem triple_bind_pre [Monad m] [MonadMorphism m (PredTrans ps) wp] {α β} {P : PreCond ps} {Q : PostCond β ps} (x : m α) (f : α → m β)
--  (hx : triple wp⟦x⟧ P (fun a => triple wp⟦f a⟧ Q, Q.2)) :
--  triple wp⟦x >>= f⟧ P R := by
--    apply le_trans hx
--    simp only [wp_bind]
--    apply wp_mono x
--    simp only [Prod.mk_le_mk, le_refl, and_true]
--    exact hf

theorem triple_extract_persistent_true {α} (x : m α) {P : Prop} {Q : PostCond α ps}
  (h : P → triple (ps:=ps) x ⌜True⌝ Q) :
  triple x ⌜P⌝ Q := by
    have : ⌜P⌝ = (sprop(⌜P⌝ ∧ ⌜True⌝) : PreCond ps) := by simp
    rw[this]
    exact triple_extract_persistent x h

/-
theorem triple_conseq_l [Monad m] [MonadMorphism m (PredTrans ps) wp] {P P' : PreCond ps} {Q : PostCond α ps}
  (x : m α) (hp : P ≤ P') (h : triple x P' Q) :
  triple x P Q := triple_conseq x hp le_rfl h

theorem triple_conseq_r [Monad m] [MonadMorphism m (PredTrans ps) wp] {P : PreCond ps} {Q Q' : PostCond α ps}
  (x : m α) (hq : Q ≤ Q') (h : triple x P Q) :
  triple x P Q' := triple_conseq x le_rfl hq h

--theorem triple_map [Monad m] [LawfulMonad m] [MonadMorphism m (PredTrans ps) wp] (f : α → β) (x : m α)
--  (h : triple x P (fun a => Q.1 (f a), Q.2)) :
--  triple (f <$> x) P Q := by
--    simp only [← bind_pure_comp]
--    apply triple_bind _ _ h
--    intro b
--    apply triple_pure
--    simp only [le_refl]

--theorem triple_seq [Monad m] [LawfulMonad m] [MonadMorphism m (PredTrans ps) wp] (f : m (α → β)) (x : m α) {Q : (α → β) → PreCond ps}
--  (hf : triple f P (Q, R.2))
--  (hx : ∀ f, triple x (Q f) (fun a => R.1 (f a), R.2)) :
--  triple (f <*> x) P R := by
--    simp only [← bind_map]
--    apply triple_bind _ _ hf ?_
--    intro f
--    apply triple_map _ _ (hx f)

theorem triple_dite {c : Prop} [Decidable c] {t : c → m α} {e : ¬c → m α} {P : PreCond ps} {Q : PostCond α ps} [Monad m] [WP m ps]
  (htrue : (h : c) → triple (t h) P Q)
  (hfalse : (h : ¬c) → triple (e h) P Q) :
  triple (dite c t e) P Q := by
    split <;> simp only [htrue, hfalse]

theorem triple_ite {c : Prop} [Decidable c] {t : m α} {e : m α} {P : PreCond ps} {Q : PostCond α ps} [Monad m] [WP m ps]
  (htrue : c → triple t P Q)
  (hfalse : ¬c → triple e P Q) :
  triple (ite c t e) P Q := by
    change triple (dite c (fun _ => t) (fun _ => e)) P Q
    exact triple_dite htrue hfalse
-/
