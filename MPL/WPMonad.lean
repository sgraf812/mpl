import MPL.WP
import MPL.MonadMorphism

open MPL

abbrev WPMonad m sh [Monad m] [WP m sh] := MonadMorphism m (PredTrans sh) wp

theorem WP.pure_apply [WP m ps] [Monad m] [WPMonad m ps] (a : α) (Q : PostCond α ps) :
  wp⟦pure (f:=m) a⟧.apply Q = Q.1 a := by
    simp only [pure_pure, PredTrans.pure_apply]

theorem WP.bind_apply [WP m ps] [Monad m] [WPMonad m ps] (x : m α) (f : α → m β) (Q : PostCond β ps) :
  wp⟦x >>= f⟧.apply Q = wp⟦x⟧.apply (fun a => wp⟦f a⟧.apply Q, Q.2) := by
    simp only [bind_bind, PredTrans.bind_apply]

theorem WP.map_apply [WP m ps] [Monad m] [WPMonad m ps] [LawfulMonad m] (f : α → β) (x : m α) (Q : PostCond β ps) :
  wp⟦f <$> x⟧.apply Q = wp⟦x⟧.apply (fun a => Q.1 (f a), Q.2) := by
    simp only [map_map, PredTrans.map_apply]

theorem WP.seq_apply [WP m ps] [Monad m] [WPMonad m ps] [LawfulMonad m] (f : m (α → β)) (x : m α) (Q : PostCond β ps) :
  wp⟦f <*> x⟧.apply Q = wp⟦f⟧.apply (fun f => wp⟦x⟧.apply (fun a => Q.1 (f a), Q.2), Q.2) := by
    simp only [seq_seq, PredTrans.seq_apply]

instance Idd.instWPMonad : WPMonad Idd .pure where
  pure_pure a := by simp only [wp, PredTrans.pure, Pure.pure, Idd.pure]
  bind_bind x f := by simp only [wp, PredTrans.pure, Bind.bind, Idd.bind, PredTrans.bind]

instance Id.instWPMonad : WPMonad Id .pure where
  pure_pure a := by simp only [wp, PredTrans.pure, Pure.pure, Id.run]
  bind_bind x f := by simp only [wp, PredTrans.pure, Bind.bind, Id.run, PredTrans.bind]

instance StateT.instWPMonad [Monad m] [WP m ps] [WPMonad m ps] : WPMonad (StateT σ m) (.arg σ ps) where
  pure_pure a := by ext; simp only [wp, pure, StateT.pure, pure_pure, PredTrans.pure,
    PredTrans.pushArg_apply]
  bind_bind x f := by ext; simp only [wp, bind, StateT.bind, bind_bind, PredTrans.bind,
    PredTrans.pushArg_apply]

instance ReaderT.instWPMonad [Monad m] [WP m ps] [WPMonad m ps] : WPMonad (ReaderT ρ m) (.arg ρ ps) where
  pure_pure a := by ext; simp only [wp, pure, ReaderT.pure, pure_pure, PredTrans.pure,
    PredTrans.pushArg_apply, PredTrans.map_apply]
  bind_bind x f := by ext; simp only [wp, bind, ReaderT.bind, bind_bind, PredTrans.bind,
    PredTrans.pushArg_apply, PredTrans.map_apply]

instance ExceptT.instWPMonad [Monad m] [WP m ps] [WPMonad m ps] : WPMonad (ExceptT ε m) (.except ε ps) where
  pure_pure a := by ext; simp only [wp, pure, ExceptT.pure, mk, pure_pure, PredTrans.pure,
    PredTrans.pushExcept_apply]
  bind_bind x f := by
    ext Q
    simp [wp, bind, ExceptT.bind, bind_bind, ExceptT.bindCont, PredTrans.bind, ExceptT.mk, PredTrans.pushExcept_apply]
    congr
    ext b
    cases b
    case error a => simp[PredTrans.pure, pure]
    case ok a => congr

instance EStateM.instWPMonad : WPMonad (EStateM ε σ) (.except ε (.arg σ .pure)) where
  pure_pure a := by simp only [wp, pure, EStateM.pure, PredTrans.pure]
  bind_bind x f := by
    ext Q s
    simp [wp, bind, EStateM.bind, eq_iff_iff, PredTrans.bind]
    cases (x s) <;> simp

instance State.instWPMonad : WPMonad (StateM σ) (.arg σ .pure) :=
  inferInstanceAs (WPMonad (StateT σ Id) (.arg σ .pure))
instance Reader.instWPMonad : WPMonad (ReaderM ρ) (.arg ρ .pure) :=
  inferInstanceAs (WPMonad (ReaderT ρ Id) (.arg ρ .pure))
theorem Except.instMonad_eq ε : @Except.instMonad ε = @ExceptT.instMonad ε Id Id.instMonad := by
  have h : Monad (Except ε) = Monad (ExceptT ε Id) := rfl
  simp[Except.instMonad, ExceptT.instMonad]
  sorry
instance Except.instWPMonad : WPMonad (Except ε) (.except ε .pure) :=
  Except.instMonad_eq ε ▸ inferInstanceAs (WPMonad (ExceptT ε Id) (.except ε .pure))
