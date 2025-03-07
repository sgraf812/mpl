import MPL.WP
import MPL.MonadMorphism

open MPL

abbrev WPMonad m sh [Monad m] [WP m sh] := MonadMorphism m (PredTrans sh) wp

instance Idd.instWPMonadMorphism : WPMonad Idd .pure where
  pure_pure a := by simp only [wp, PredTrans.pure, Pure.pure, Idd.pure]
  bind_bind x f := by simp only [wp, PredTrans.pure, Bind.bind, Idd.bind, PredTrans.bind]

instance Id.instWPMonadMorphism : WPMonad Id .pure where
  pure_pure a := by simp only [wp, PredTrans.pure, Pure.pure, Id.run]
  bind_bind x f := by simp only [wp, PredTrans.pure, Bind.bind, Id.run, PredTrans.bind]

instance StateT.instWPMonadMorphism [Monad m] [WP m ps] [WPMonad m ps] : WPMonad (StateT σ m) (.arg σ ps) where
  pure_pure a := by ext; simp [wp, pure, StateT.pure, PredTrans.pure]
  bind_bind x f := by ext; simp [wp, Bind.bind, bind, PredTrans.bind, StateT.bind]

instance ReaderT.instWPMonadMorphism [Monad m] [WP m ps] [WPMonad m ps] : WPMonad (ReaderT ρ m) (.arg ρ ps) where
  pure_pure a := by ext; simp [wp, pure, ReaderT.pure, PredTrans.pure]
  bind_bind x f := by ext; simp [wp, Bind.bind, bind, PredTrans.bind, ReaderT.bind]

instance ExceptT.instWPMonadMorphism [Monad m] [WP m ps] [WPMonad m ps] : WPMonad (ExceptT ε m) (.except ε ps) where
  pure_pure a := by ext; simp [wp, PredTrans.pure, pure, ExceptT.pure, ExceptT.mk, pure_pure]
  bind_bind x f := by
    ext Q
    simp [wp, bind, ExceptT.bind, bind_bind, ExceptT.bindCont, PredTrans.bind, ExceptT.mk]
    congr
    ext b
    cases b
    case error a => simp[PredTrans.pure, pure]
    case ok a => congr

instance EStateM.instWPMonadMorphism : WPMonad (EStateM ε σ) (.except ε (.arg σ .pure)) where
  pure_pure a := by simp [wp, PredTrans.pure, pure, EStateM.pure]
  bind_bind x f := by
    ext Q s
    simp [wp, bind, EStateM.bind, eq_iff_iff, PredTrans.bind]
    cases (x s) <;> simp

instance State.instWPMonadMorphism : WPMonad (StateM σ) (.arg σ .pure) :=
  inferInstanceAs (WPMonad (StateT σ Id) (.arg σ .pure))
instance Reader.instWPMonadMorphism : WPMonad (ReaderM ρ) (.arg ρ .pure) :=
  inferInstanceAs (WPMonad (ReaderT ρ Id) (.arg ρ .pure))
theorem Except.instMonad_eq ε : @Except.instMonad ε = @ExceptT.instMonad ε Id Id.instMonad := by
  have h : Monad (Except ε) = Monad (ExceptT ε Id) := rfl
  simp[Except.instMonad, ExceptT.instMonad]
  sorry
instance Except.instWPMonadMorphism : WPMonad (Except ε) (.except ε .pure) :=
  Except.instMonad_eq ε ▸ inferInstanceAs (WPMonad (ExceptT ε Id) (.except ε .pure))
