import MPL.WPMonad

namespace MPL

def triple {ps : PredShape} {α} (x : PredTrans ps α) (P : PreCond ps) (Q : PostCond α ps) : Prop :=
  P ≤ x.apply Q

notation:lead "⦃" P "⦄ " x:lead " ⦃" Q "⦄" =>
  triple x P Q
notation:lead "⦃" P "⦄ " x:lead " ⦃⇓" v " | " Q "⦄" =>
  ⦃P⦄ x ⦃PostCond.total fun v => Q⦄

/-
theorem triple_conseq {m : Type → Type} [WP m ps] {α} (x : m α) {P P' : PreCond ps} {Q Q' : PostCond α ps}
  (hp : P ≤ P' := by simp) (hq : Q' ≤ Q := by simp) (h : triple x P' Q') :
  triple x P Q := by
    apply le_trans hp
    apply le_trans h
    apply wp_mono x Q' Q hq

theorem triple_extract_persistent {m : Type → Type} [Monad m] [WP m ps] [WPMonad m ps] {P : Prop} {P' : PreCond ps} {Q : PostCond α ps}
  (x : m α) (h : P → triple x P' Q) :
  triple x (PreCond.pure P ⊓ P') Q := PreCond.imp_pure_extract_l h

theorem triple_pure {m : Type → Type} [Monad m] [WP m ps] [WPMonad m ps] {α} {Q : PostCond α ps} (a : α) (himp : P ≤ Q.1 a) :
  triple (pure (f:=m) a) P Q := by apply le_trans himp (by simp only [wp_pure, PredTrans.pure_apply, le_refl])

theorem triple_bind {m : Type → Type} [Monad m] [WP m ps] [WPMonad m ps] {α β} {P : PreCond ps} {Q : α → PreCond ps} {R : PostCond β ps} (x : m α) (f : α → m β)
  (hx : triple x P (Q, R.2))
  (hf : ∀ b, triple (f b) (Q b) R) :
  triple (x >>= f) P R := by
    apply le_trans hx
    simp only [wp_bind]
    apply wp_mono x
    simp only [Prod.mk_le_mk, le_refl, and_true]
    exact hf

theorem triple_conseq_l {m : Type → Type} [Monad m] [WP m ps] [WPMonad m ps] {P P' : PreCond ps} {Q : PostCond α ps}
  (x : m α) (hp : P ≤ P') (h : triple x P' Q) :
  triple x P Q := triple_conseq x hp le_rfl h

theorem triple_conseq_r {m : Type → Type} [Monad m] [WP m ps] [WPMonad m ps] {P : PreCond ps} {Q Q' : PostCond α ps}
  (x : m α) (hq : Q ≤ Q') (h : triple x P Q) :
  triple x P Q' := triple_conseq x le_rfl hq h

--theorem triple_map {m : Type → Type} [Monad m] [LawfulMonad m] [WP m ps] [WPMonad m ps] (f : α → β) (x : m α)
--  (h : triple x P (fun a => Q.1 (f a), Q.2)) :
--  triple (f <$> x) P Q := by
--    simp only [← bind_pure_comp]
--    apply triple_bind _ _ h
--    intro b
--    apply triple_pure
--    simp only [le_refl]

--theorem triple_seq {m : Type → Type} [Monad m] [LawfulMonad m] [WP m ps] [WPMonad m ps] (f : m (α → β)) (x : m α) {Q : (α → β) → PreCond ps}
--  (hf : triple f P (Q, R.2))
--  (hx : ∀ f, triple x (Q f) (fun a => R.1 (f a), R.2)) :
--  triple (f <*> x) P R := by
--    simp only [← bind_map]
--    apply triple_bind _ _ hf ?_
--    intro f
--    apply triple_map _ _ (hx f)

theorem triple_extract_persistent_true {m : Type → Type} [Monad m] [LawfulMonad m] [WP m ps] [WPMonad m ps] {P : Prop} {Q : PostCond α ps}
  (x : m α) (h : P → triple x (PreCond.pure True) Q) :
  triple x (PreCond.pure P) Q := by
    have : PreCond.pure P = (PreCond.pure P ⊓ PreCond.pure True : PreCond ps) := by simp
    rw[this]
    exact triple_extract_persistent x h

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
