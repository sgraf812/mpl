import MPL.WP
import MPL.MonadMorphism

open MPL

instance Idd.instWPMonadMorphism : MonadMorphism Idd (PredTrans .pure) wp where
  pure_pure a := by simp only [wp, PredTrans.pure, Pure.pure, Idd.pure]
  bind_bind x f := by simp only [wp, PredTrans.pure, Bind.bind, Idd.bind, PredTrans.bind]

instance Id.instWPMonadMorphism : MonadMorphism Id (PredTrans .pure) wp where
  pure_pure a := by simp only [wp, PredTrans.pure, Pure.pure, Id.run]
  bind_bind x f := by simp only [wp, PredTrans.pure, Bind.bind, Id.run, PredTrans.bind]

instance StateT.instWPMonadMorphism [Monad m] [WP m ps] [MonadMorphism m (PredTrans ps) wp] : MonadMorphism (StateT σ m) (PredTrans (.arg σ ps)) wp where
  pure_pure a := by ext; simp [wp, pure, StateT.pure, PredTrans.pure]
  bind_bind x f := by ext; simp [wp, Bind.bind, bind, PredTrans.bind, StateT.bind]

instance ReaderT.instWPMonadMorphism [Monad m] [WP m ps] [MonadMorphism m (PredTrans ps) wp] : MonadMorphism (ReaderT ρ m) (PredTrans (.arg ρ ps)) wp where
  pure_pure a := by ext; simp [wp, pure, ReaderT.pure, PredTrans.pure]
  bind_bind x f := by ext; simp [wp, Bind.bind, bind, PredTrans.bind, ReaderT.bind]

instance ExceptT.instWPMonadMorphism [Monad m] [WP m ps] [MonadMorphism m (PredTrans ps) wp] : MonadMorphism (ExceptT ε m) (PredTrans (.except ε ps)) wp where
  pure_pure a := by ext; simp [wp, PredTrans.pure, pure, ExceptT.pure, ExceptT.mk, pure_pure]
  bind_bind x f := by
    ext Q
    simp [wp, bind, ExceptT.bind, bind_bind, ExceptT.bindCont, PredTrans.bind, ExceptT.mk]
    congr
    ext b
    cases b
    case error a => simp[PredTrans.pure, pure]
    case ok a => congr

instance EStateM.instWPMonadMorphism : MonadMorphism (EStateM ε σ) (PredTrans (.except ε (.arg σ .pure))) wp where
  pure_pure a := by simp [wp, PredTrans.pure, pure, EStateM.pure]
  bind_bind x f := by
    ext Q s
    simp [wp, bind, EStateM.bind, eq_iff_iff, PredTrans.bind]
    cases (x s) <;> simp

instance State.instWPMonadMorphism : MonadMorphism (StateM σ) (PredTrans (.arg σ .pure)) wp :=
  inferInstanceAs (MonadMorphism (StateT σ Id) (PredTrans (.arg σ .pure)) wp)
instance Reader.instWPMonadMorphism : MonadMorphism (ReaderM ρ) (PredTrans (.arg ρ .pure)) wp :=
  inferInstanceAs (MonadMorphism (ReaderT ρ Id) (PredTrans (.arg ρ .pure)) wp)
theorem Except.instMonad_eq ε : @Except.instMonad ε = @ExceptT.instMonad ε Id Id.instMonad := by
  have h : Monad (Except ε) = Monad (ExceptT ε Id) := rfl
  simp[Except.instMonad, ExceptT.instMonad]
  sorry
instance Except.instWPMonadMorphism : MonadMorphism (Except ε) (PredTrans (.except ε .pure)) wp :=
  Except.instMonad_eq ε ▸ inferInstanceAs (MonadMorphism (ExceptT ε Id) (PredTrans (.except ε .pure)) wp)
