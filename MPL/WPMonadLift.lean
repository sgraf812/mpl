import MPL.WPMonad

namespace MPL

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
theorem MonadStateOf.wp_get [WP m msh] [WP n nsh] [MonadLift m n] [MonadLift (PredTrans msh) (PredTrans nsh)] [MonadStateOf σ m] [WPMonadLift m n msh nsh] :
  wp (MonadStateOf.get : n σ) = MonadLift.monadLift (wp (MonadStateOf.get : m σ)) := by
    simp [MonadStateOf.get, liftM, monadLift]

@[simp]
theorem MonadState.wp_get [WP m sh] [MonadStateOf σ m] :
  wp (MonadState.get : m σ) = wp (MonadStateOf.get : m σ) := rfl

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
theorem ExceptT.wp_throw [Monad m] [WP m stack] [WPMonad m stack] :
  wp (throw e : ExceptT ε m α) = PredTrans.throw e := by
    simp[wp, pure, PredTrans.pure, PredTrans.throw]
