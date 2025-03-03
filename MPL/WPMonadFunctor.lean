import MPL.WPMonad

namespace MPL

open MonadFunctor renaming monadMap → mmap

class LawfulMonadFunctor (m : semiOutParam (Type → Type)) (n : Type → Type) [Monad n] [MonadFunctor m n] where
  monadMap_id {α} :
    mmap (m:=m) id = (id : n α → n α)
  monadMap_comp {α} (g f : ∀ {β}, m β → m β) :
    mmap (m:=m) (fun a => f (g a)) = fun (x : n α) => mmap (m:=m) f (mmap (m:=m) g x)
  monadMap_pure {α} (f : ∀ {β}, m β → m β) (a : α) :
    mmap (m:=m) f (pure a) = pure (f:=n) a
  monadMap_bind {α} (μ : ∀ {β}, m β → m β) (x : n α) (f : α → n β) :
    mmap (m:=m) μ (do let a ← x; f a) = (do let a ← mmap (m:=m) μ x; mmap (m:=m) μ (f a))

/-
theorem LawfulMonadFunctor.monadMap_map {m n : Type → Type} [Monad m] [Monad n] [MonadFunctor m n] [LawfulMonad m] [LawfulMonad n] [LawfulMonadFunctor m n]
    {α β} (f : α → β) (x : m α) :
    MonadFunctor.monadMap (f <$> x) = f <$> (MonadFunctor.monadMap x : n α) := by
    simp[liftM, MonadLift.monadLift, ←bind_pure_comp, monadMap_bind, monadMap_pure]

theorem LawfulMonadFunctor.lift_seq {m n : Type → Type} [Monad m] [Monad n] [MonadLift m n] [LawfulMonad m] [LawfulMonad n] [LawfulMonadFunctor m n]
    {α β} (f : m (α → β)) (x : m α) :
    MonadFunctor.monadMap (f <*> x) = (MonadFunctor.monadMap f : n (α → β)) <*> (MonadFunctor.monadMap x : n α) := by
    simp[liftM, MonadLift.monadLift, ←bind_map, monadMap_bind, lift_map]
-/

instance StateT.instLawfulMonadFunctor [Monad m] [LawfulMonad m] : LawfulMonadFunctor m (StateT σ m) where
  monadMap_id := by intro _; rfl
  monadMap_comp := by intro _; simp only [mmap, implies_true]
  monadMap_pure := by intro _; simp[mmap]
  monadMap_bind := by ext; simp[liftM, MonadLift.monadLift, StateT.lift]

instance ReaderT.instLawfulMonadFunctor [Monad m] [LawfulMonad m] : LawfulMonadFunctor m (ReaderT ρ m) where
  monadMap_pure x := by ext; simp[liftM, MonadLift.monadLift, ReaderT.run, pure, ReaderT.pure]
  monadMap_bind x f := by ext; simp[liftM, MonadLift.monadLift, ReaderT.run, bind, ReaderT.bind]

instance ExceptT.instLawfulMonadFunctor [Monad m] [LawfulMonad m] : LawfulMonadFunctor m (ExceptT ε m) where
  monadMap_pure x := by ext; simp[liftM, MonadLift.monadLift, ExceptT.lift]
  monadMap_bind x f := by ext; simp[liftM, MonadLift.monadLift, ExceptT.lift, ExceptT.mk, bind, ExceptT.bind, ExceptT.bindCont]

instance PredTrans.instLawfulMonadFunctorArg : LawfulMonadFunctor (PredTrans ps) (PredTrans (.arg σ ps)) where
  monadMap_pure x := by ext; simp
  monadMap_bind x f := by ext Q σ; simp[bind, PredTrans.bind]

instance PredTrans.instLawfulMonadFunctorDropFail : LawfulMonadFunctor (PredTrans ps) (PredTrans (.except ε ps)) where
  monadMap_pure x := by ext; simp
  monadMap_bind x f := by ext Q; simp[bind, PredTrans.bind]

attribute [simp] LawfulMonadFunctor.monadMap_pure LawfulMonadFunctor.monadMap_bind LawfulMonadFunctor.lift_map LawfulMonadFunctor.lift_seq

class WPMonadLift (m : semiOutParam (Type → Type)) (n : Type → Type) (psm : outParam PredShape) (psn : outParam PredShape)
  [WP m psm] [WP n psn] [MonadLift m n] [MonadLift (PredTrans psm) (PredTrans psn)] where
  wp_monadLift {x : m α} :
    wp (MonadLift.monadLift x : n α) = MonadLift.monadLift (wp x)

export WPMonadLift (wp_monadLift)
attribute [simp] wp_monadLift

instance StateT.instWPMonadLift [Monad m] [WP m psm] [LawfulMonad m] [WPMonad m psm] : WPMonadLift m (StateT σ m) psm (.arg σ psm) where
  wp_monadLift := by simp[wp, liftM, MonadLift.monadLift, StateT.lift, PredTrans.frame_arg]

instance ReaderT.instWPMonadLift [Monad m] [WP m psm] [LawfulMonad m] [WPMonad m psm] : WPMonadLift m (ReaderT ρ m) psm (.arg ρ psm) where
  wp_monadLift := by simp[wp, MonadLift.monadLift, PredTrans.frame_arg]

instance ExceptT.instWPMonadLift [Monad m] [WP m psm] [LawfulMonad m] [WPMonad m psm] : WPMonadLift m (ExceptT ε m) psm (.except ε psm) where
  wp_monadLift := by simp[wp, liftM, MonadLift.monadLift, ExceptT.lift, Function.comp_def, PredTrans.drop_fail_cond]
-/

end MPL
