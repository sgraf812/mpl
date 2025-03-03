import MPL.WP

namespace MPL

class WPMonad (m : Type → Type) (ps : outParam PredShape) [Monad m] [WP m ps] where
  wp_pure {α} (a : α) :
    wp (m:=m) (pure a) = pure a
  wp_bind {α β} (x : m α) (f : α → m β) :
    wp⟦do let a ← x; f a⟧ = do let a ← wp⟦x⟧; wp⟦f a⟧

attribute [simp] WPMonad.wp_pure WPMonad.wp_bind

@[simp]
theorem WPMonad.wp_map {m : Type → Type} [Monad m] [LawfulMonad m] [WP m ps] [WPMonad m ps] (f : α → β) (x : m α) :
  wp⟦f <$> x⟧ = f <$> wp⟦x⟧ := by
    simp [← bind_pure_comp, wp_bind, wp_pure]

@[simp]
theorem WPMonad.wp_seq {m : Type → Type} [Monad m] [LawfulMonad m] [WP m ps] [WPMonad m ps] (f : m (α → β)) (x : m α) :
  wp⟦f <*> x⟧ = wp⟦f⟧ <*> wp⟦x⟧ := by
    simp [← bind_map, wp_bind, wp_map]

--theorem WPMonad.wp_pure_conseq {m : Type → Type} [Monad m] [WP m ps] [WPMonad m ps] {α} {P : PreCond ps} {Q : PostCond α ps} (a : α)
--    (himp : P ≤ Q.1 a) : P ≤ wp (m:=m) (pure a) Q := by rw[wp_pure a]; exact himp

-- theorem WPMonad.wp_bind_conseq_f {m : Type → Type} [Monad m] [WP m ps] [WPMonad m ps] {α β} {P : PostCond α ps} {Q : PostCond β ps} (x : m α) (f : α → m β)
--     (hf : ∀a, P.1 a ≤ wp (f a) Q) (herror : P.2 ≤ Q.2) :
--     wp x P ≤ wp (x >>= f) Q := by rw[wp_bind x f]; exact wp_mono x P (fun a => wp (f a) Q, Q.2) ⟨hf, herror⟩

--theorem WPMonad.wp_mono_2 {m : Type → Type} [Monad m] [WP m ps] [WPMonad m ps] {α} (x : m α) (Q₁ Q₂ : PostCond α ps)
--    (h1 : Q₁.1 ≤ Q₂.1) (h2 : Q₁.2 ≤ Q₂.2) :
--    wp x Q₁ ≤ wp x Q₂ := wp_mono x _ _ ⟨h1,h2⟩

-- theorem WPMonad.wp_seq_f {m : Type → Type} [Monad m] [LawfulMonad m] [WP m ps] [WPMonad m ps] (f : m (α → β)) (x : m α) {Q : PostCond β ps}
--     (hx : ∀f, P.1 f ≤ wp x (fun a => Q.1 (f a), Q.2)) (herror : P.2 ≤ Q.2) :
--   wp f P ≤ wp (f <*> x) Q := le_trans (wp_mono f P _ ⟨hx, herror⟩) (wp_seq f x)

export WPMonad (wp_pure wp_bind wp_map wp_seq)

end MPL
open MPL

instance Idd.instWPMonad : WPMonad Idd .pure where
  wp_pure a := by simp only [wp, PredTrans.pure, Pure.pure, Idd.pure]
  wp_bind x f := by simp only [wp, PredTrans.pure, Bind.bind, Idd.bind, PredTrans.bind]

instance Id.instWPMonad : WPMonad Id .pure where
  wp_pure a := by simp only [wp, PredTrans.pure, Pure.pure, Id.run]
  wp_bind x f := by simp only [wp, PredTrans.pure, Bind.bind, Id.run, PredTrans.bind]

instance StateT.instWPMonad [Monad m] [WP m ps] [WPMonad m ps] : WPMonad (StateT σ m) (.arg σ ps) where
  wp_pure a := by simp [wp, PredTrans.pure, pure, StateT.pure, wp_pure]
  wp_bind x f := by simp [wp, PredTrans.pure, Bind.bind, bind, PredTrans.bind, StateT.bind]

instance ReaderT.instWPMonad [Monad m] [WP m ps] [WPMonad m ps] : WPMonad (ReaderT ρ m) (.arg ρ ps) where
  wp_pure a := by simp [wp, PredTrans.pure, pure, ReaderT.pure, wp_pure]
  wp_bind x f := by simp [wp, PredTrans.pure, Bind.bind, bind, PredTrans.bind, ReaderT.bind]

instance ExceptT.instWPMonad [Monad m] [WP m ps] [WPMonad m ps] : WPMonad (ExceptT ε m) (.except ε ps) where
  wp_pure a := by simp [wp, PredTrans.pure, pure, ExceptT.pure, wp_pure]
  wp_bind x f := by
    ext Q
    simp [wp, bind, ExceptT.bind, wp_bind, ExceptT.bindCont, PredTrans.bind]
    congr
    ext b
    cases b
    case error a => simp[PredTrans.pure, pure]
    case ok a => congr

instance EStateM.instWPMonad : WPMonad (EStateM ε σ) (.except ε (.arg σ .pure)) where
  wp_pure a := by simp [wp, PredTrans.pure, pure, EStateM.pure]
  wp_bind x f := by
    ext Q s
    simp [wp, bind, EStateM.bind, eq_iff_iff, PredTrans.bind]
    cases (x s) <;> simp

instance State.instWPMonad : WPMonad (StateM σ) (.arg σ .pure) := inferInstanceAs (WPMonad (StateT σ Id) (.arg σ .pure))
instance Reader.instWPMonad : WPMonad (ReaderM ρ) (.arg ρ .pure) := inferInstanceAs (WPMonad (ReaderT ρ Id) (.arg ρ .pure))
theorem Except.instMonad_eq ε : @Except.instMonad ε = @ExceptT.instMonad ε Id Id.instMonad := by
  have h : Monad (Except ε) = Monad (ExceptT ε Id) := rfl
  simp[Except.instMonad, ExceptT.instMonad]
  sorry
instance Except.instWPMonad : WPMonad (Except ε) (.except ε .pure) := Except.instMonad_eq ε ▸ inferInstanceAs (WPMonad (ExceptT ε Id) (.except ε .pure))
