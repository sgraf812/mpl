import MPL.WPMonad

namespace MPL

-- TODO: Upstream
class LawfulMonadLift (m : semiOutParam (Type → Type)) (n : Type → Type) [Monad m] [Monad n] [MonadLift m n] where
  lift_pure {α} (x : α) :
    MonadLift.monadLift (pure (f:=m) x) = pure (f:=n) x
  lift_bind {α β} (x : m α) (f : α → m β) :
    MonadLift.monadLift (do let a ← x; f a) = do let a ← (MonadLift.monadLift x : n α); MonadLift.monadLift (f a)

theorem LawfulMonadLift.lift_map {m n : Type → Type} [Monad m] [Monad n] [MonadLift m n] [LawfulMonad m] [LawfulMonad n] [LawfulMonadLift m n]
    {α β} (f : α → β) (x : m α) :
    MonadLift.monadLift (f <$> x) = f <$> (MonadLift.monadLift x : n α) := by
    simp[liftM, MonadLift.monadLift, ←bind_pure_comp, lift_bind, lift_pure]

theorem LawfulMonadLift.lift_seq {m n : Type → Type} [Monad m] [Monad n] [MonadLift m n] [LawfulMonad m] [LawfulMonad n] [LawfulMonadLift m n]
    {α β} (f : m (α → β)) (x : m α) :
    MonadLift.monadLift (f <*> x) = (MonadLift.monadLift f : n (α → β)) <*> (MonadLift.monadLift x : n α) := by
    simp[liftM, MonadLift.monadLift, ←bind_map, lift_bind, lift_map]

instance StateT.instLawfulMonadLift [Monad m] [LawfulMonad m] : LawfulMonadLift m (StateT σ m) where
  lift_pure x := by ext; simp[liftM, MonadLift.monadLift, StateT.lift]
  lift_bind x f := by ext; simp[liftM, MonadLift.monadLift, StateT.lift]

instance ReaderT.instLawfulMonadLift [Monad m] [LawfulMonad m] : LawfulMonadLift m (ReaderT ρ m) where
  lift_pure x := by ext; simp[liftM, MonadLift.monadLift, ReaderT.run, pure, ReaderT.pure]
  lift_bind x f := by ext; simp[liftM, MonadLift.monadLift, ReaderT.run, bind, ReaderT.bind]

instance ExceptT.instLawfulMonadLift [Monad m] [LawfulMonad m] : LawfulMonadLift m (ExceptT ε m) where
  lift_pure x := by ext; simp[liftM, MonadLift.monadLift, ExceptT.lift]
  lift_bind x f := by ext; simp[liftM, MonadLift.monadLift, ExceptT.lift, ExceptT.mk, bind, ExceptT.bind, ExceptT.bindCont]

instance PredTrans.instLawfulMonadLiftArg : LawfulMonadLift (PredTrans ps) (PredTrans (.arg σ ps)) where
  lift_pure x := by ext; simp
  lift_bind x f := by ext Q σ; simp[bind, PredTrans.bind]

instance PredTrans.instLawfulMonadLiftDropFail : LawfulMonadLift (PredTrans ps) (PredTrans (.except ε ps)) where
  lift_pure x := by ext; simp
  lift_bind x f := by ext Q; simp[bind, PredTrans.bind]

attribute [simp] LawfulMonadLift.lift_pure LawfulMonadLift.lift_bind LawfulMonadLift.lift_map LawfulMonadLift.lift_seq

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

end MPL
open MPL

@[simp]
theorem StateT.wp_get [WP m sh] [Monad m] [WPMonad m sh] :
  wp (MonadStateOf.get : StateT σ m σ) = PredTrans.get := by
    simp[wp, MonadState.get, getThe, MonadStateOf.get, StateT.get, pure, PredTrans.pure, PredTrans.get]

@[simp]
theorem MonadState.wp_get [WP m sh] [MonadStateOf σ m] :
  wp (MonadState.get : m σ) = wp (MonadStateOf.get : m σ) := rfl

@[simp]
theorem MonadStateOf.wp_get [WP m msh] [WP n nsh] [MonadLift m n] [MonadLift (PredTrans msh) (PredTrans nsh)] [MonadStateOf σ m] [WPMonadLift m n msh nsh] :
  wp (MonadStateOf.get : n σ) = MonadLift.monadLift (wp (MonadStateOf.get : m σ)) := by
    simp [MonadStateOf.get, liftM, monadLift]

@[simp]
theorem StateT.wp_set [WP m sh] [Monad m] [WPMonad m sh] (x : σ) :
  wp (MonadState.set x : StateT σ m PUnit) = PredTrans.set x := by
    simp[wp, MonadState.set, MonadStateOf.set, StateT.set, pure, PredTrans.pure, PredTrans.set]

@[simp]
theorem MonadStateOf.wp_set [WP m msh] [WP n nsh] [MonadLift m n] [MonadLift (PredTrans msh) (PredTrans nsh)] [MonadStateOf σ m] [WPMonadLift m n msh nsh] :
  wp (MonadStateOf.set x : n PUnit) = MonadLift.monadLift (wp (MonadStateOf.set (σ:=σ) x : m PUnit)) := by
    simp [MonadStateOf.set, liftM, monadLift]

@[simp]
theorem MonadState.wp_set [WP m sh] [MonadStateOf σ m] :
  wp (MonadState.set x : m PUnit) = wp (MonadStateOf.set x : m PUnit) := rfl

@[simp]
theorem StateT.wp_modifyGet [WP m sh] [Monad m] [WPMonad m sh]
  (f : σ → α × σ) :
  wp (MonadStateOf.modifyGet f : StateT σ m α) = PredTrans.modifyGet f := by
    simp[wp, MonadStateOf.modifyGet, StateT.modifyGet, pure, PredTrans.pure, PredTrans.modifyGet]

@[simp]
theorem MonadState.wp_modifyGet [WP m sh] [MonadStateOf σ m] (f : σ → α × σ) :
  wp (MonadState.modifyGet f : m α) = wp (MonadStateOf.modifyGet f : m α) := rfl

@[simp]
theorem MonadStateOf.wp_modifyGet [WP m msh] [WP n nsh] [MonadLift m n] [MonadLift (PredTrans msh) (PredTrans nsh)] [MonadStateOf σ m] [WPMonadLift m n msh nsh]
  (f : σ → α × σ) :
  wp (MonadStateOf.modifyGet f : n α) = MonadLift.monadLift (wp (MonadStateOf.modifyGet f : m α)) := by
    simp [MonadStateOf.modifyGet, liftM, monadLift]

@[simp]
theorem MonadState.wp_modify [WP m msh] [MonadStateOf σ m]
  (f : σ → σ) :
  wp (modify f : m PUnit) = wp ((MonadStateOf.modifyGet fun s => ((), f s)) : m PUnit) := rfl

@[simp]
theorem ExceptT.wp_throw [Monad m] [WP m stack] [WPMonad m stack] :
  wp (throw e : ExceptT ε m α) = PredTrans.throw e := by
    simp[wp, pure, PredTrans.pure, PredTrans.throw]
