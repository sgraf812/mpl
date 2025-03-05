import MPL.WPMonad

namespace MPL

-- TODO: Upstream
class LawfulMonadLift (m : semiOutParam (Type → Type)) (n : Type → Type) [Monad m] [Monad n] [MonadLift m n] where
  monadLift_pure {α} (x : α) :
    MonadLift.monadLift (pure (f:=m) x) = pure (f:=n) x
  monadLift_bind {α β} (x : m α) (f : α → m β) :
    MonadLift.monadLift (do let a ← x; f a) = do let a ← (MonadLift.monadLift x : n α); MonadLift.monadLift (f a)

theorem LawfulMonadLift.monadLift_map {m n : Type → Type} [Monad m] [Monad n] [MonadLift m n] [LawfulMonad m] [LawfulMonad n] [LawfulMonadLift m n]
    {α β} (f : α → β) (x : m α) :
    MonadLift.monadLift (f <$> x) = f <$> (MonadLift.monadLift x : n α) := by
    simp[liftM, MonadLift.monadLift, ←bind_pure_comp, monadLift_bind, monadLift_pure]

theorem LawfulMonadLift.monadLift_seq {m n : Type → Type} [Monad m] [Monad n] [MonadLift m n] [LawfulMonad m] [LawfulMonad n] [LawfulMonadLift m n]
    {α β} (f : m (α → β)) (x : m α) :
    MonadLift.monadLift (f <*> x) = (MonadLift.monadLift f : n (α → β)) <*> (MonadLift.monadLift x : n α) := by
    simp[liftM, MonadLift.monadLift, ←bind_map, monadLift_bind, monadLift_map]

instance StateT.instLiftMonadMorphism [Monad m] [LawfulMonad m] : MonadMorphism m (StateT σ m) MonadLift.monadLift where
  pure_pure x := by ext; simp[liftM, MonadLift.monadLift, StateT.lift]
  bind_bind x f := by ext; simp[liftM, MonadLift.monadLift, StateT.lift]

instance ReaderT.instLiftMonadMorphism [Monad m] [LawfulMonad m] : MonadMorphism m (ReaderT ρ m) MonadLift.monadLift where
  pure_pure x := by ext; simp[liftM, MonadLift.monadLift, ReaderT.run, pure, ReaderT.pure]
  bind_bind x f := by ext; simp[liftM, MonadLift.monadLift, ReaderT.run, bind, ReaderT.bind]

instance ExceptT.instLiftMonadMorphism [Monad m] [LawfulMonad m] : MonadMorphism m (ExceptT ε m) MonadLift.monadLift where
  pure_pure x := by ext; simp[liftM, MonadLift.monadLift, ExceptT.lift]
  bind_bind x f := by ext; simp[liftM, MonadLift.monadLift, ExceptT.lift, ExceptT.mk, bind, ExceptT.bind, ExceptT.bindCont]

instance PredTrans.instLiftMonadMorphismArg : MonadMorphism (PredTrans ps) (PredTrans (.arg σ ps)) MonadLift.monadLift where
  pure_pure x := by ext; simp
  bind_bind x f := by ext Q σ; simp[bind, PredTrans.bind]

instance PredTrans.instLiftMonadMorphismDropFail : MonadMorphism (PredTrans ps) (PredTrans (.except ε ps)) MonadLift.monadLift where
  pure_pure x := by ext; simp
  bind_bind x f := by ext Q; simp[bind, PredTrans.bind]

class WPMonadLift (m : semiOutParam (Type → Type)) (n : Type → Type) (psm : outParam PredShape) (psn : outParam PredShape)
  [WP m psm] [WP n psn] [MonadLift m n] [MonadLift (PredTrans psm) (PredTrans psn)] where
  wp_monadLift {x : m α} :
    wp (MonadLift.monadLift x : n α) = MonadLift.monadLift (wp x)

export WPMonadLift (wp_monadLift)
attribute [simp] wp_monadLift

instance StateT.instWPMonadLift [Monad m] [WP m psm] [LawfulMonad m] [MonadMorphism m (PredTrans psm) wp] : WPMonadLift m (StateT σ m) psm (.arg σ psm) where
  wp_monadLift := by intro _ _; ext; simp[wp, liftM, monadLift, MonadLift.monadLift, StateT.lift]

instance ReaderT.instWPMonadLift [Monad m] [WP m psm] [LawfulMonad m] [MonadMorphism m (PredTrans psm) wp] : WPMonadLift m (ReaderT ρ m) psm (.arg ρ psm) where
  wp_monadLift := by intro _ _; ext; simp[wp, liftM, monadLift, MonadLift.monadLift, StateT.lift]

instance ExceptT.instWPMonadLift [Monad m] [WP m psm] [LawfulMonad m] [MonadMorphism m (PredTrans psm) wp] : WPMonadLift m (ExceptT ε m) psm (.except ε psm) where
  wp_monadLift := by intro _ _; ext; simp[wp, liftM, monadLift, MonadLift.monadLift, ExceptT.lift, Function.comp_def, ExceptT.mk]

end MPL
open MPL

@[simp]
theorem ReaderT.wp_read [Monad m] [WP m psm] [MonadMorphism m (PredTrans psm) wp] :
  wp (MonadReaderOf.read : ReaderT ρ m ρ) = PredTrans.get := by
    ext; simp[wp, MonadReaderOf.read, ReaderT.read, pure, PredTrans.pure, PredTrans.get]

@[simp]
theorem MonadReaderOf.wp_readThe [MonadReaderOf ρ m] [WP m sh] :
  wp (readThe ρ : m ρ) = wp (MonadReaderOf.read : m ρ) := by
    simp only [readThe]

@[simp]
theorem MonadReader.wp_read [MonadReaderOf ρ m] [WP m sh] :
  wp (MonadReader.read : m ρ) = wp (MonadReaderOf.read : m ρ) := by
    simp only [read, MonadReaderOf.wp_readThe]

@[simp]
theorem MonadReaderOf.wp_read [MonadReaderOf ρ m] [WP m msh] [WP n nsh] [MonadLift m n] [MonadLift (PredTrans msh) (PredTrans nsh)] [WPMonadLift m n msh nsh] :
  wp (MonadReaderOf.read : n ρ) = wp (MonadReaderOf.read : m ρ) := by
    simp only [read, liftM, monadLift, wp_monadLift, MonadReader.wp_read]

@[simp]
theorem StateT.wp_get [WP m psm] [Monad m] [MonadMorphism m (PredTrans psm) wp] :
  wp (MonadStateOf.get : StateT σ m σ) = PredTrans.get := by
    ext; simp[wp, MonadState.get, getThe, MonadStateOf.get, StateT.get, pure, PredTrans.pure, PredTrans.get]

@[simp]
theorem MonadState.wp_get [WP m sh] [MonadStateOf σ m] :
  wp (MonadState.get : m σ) = wp (MonadStateOf.get : m σ) := rfl

@[simp]
theorem MonadStateOf.wp_get [WP m msh] [WP n nsh] [MonadLift m n] [MonadLift (PredTrans msh) (PredTrans nsh)] [MonadStateOf σ m] [WPMonadLift m n msh nsh] :
  wp (MonadStateOf.get : n σ) = MonadLift.monadLift (wp (MonadStateOf.get : m σ)) := by
    simp [MonadStateOf.get, liftM, monadLift]

@[simp]
theorem StateT.wp_set [WP m sh] [Monad m] [MonadMorphism m (PredTrans sh) wp] (x : σ) :
  wp (MonadState.set x : StateT σ m PUnit) = PredTrans.set x := by
    ext; simp[wp, MonadState.set, MonadStateOf.set, StateT.set, pure, PredTrans.pure, PredTrans.set]

@[simp]
theorem MonadStateOf.wp_set [WP m msh] [WP n nsh] [MonadLift m n] [MonadLift (PredTrans msh) (PredTrans nsh)] [MonadStateOf σ m] [WPMonadLift m n msh nsh] :
  wp (MonadStateOf.set x : n PUnit) = MonadLift.monadLift (wp (MonadStateOf.set (σ:=σ) x : m PUnit)) := by
    simp [MonadStateOf.set, liftM, monadLift]

@[simp]
theorem MonadState.wp_set [WP m sh] [MonadStateOf σ m] :
  wp (MonadState.set x : m PUnit) = wp (MonadStateOf.set x : m PUnit) := rfl

@[simp]
theorem StateT.wp_modifyGet [WP m sh] [Monad m] [MonadMorphism m (PredTrans sh) wp]
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
theorem ExceptT.wp_throw [Monad m] [WP m ps] [MonadMorphism m (PredTrans ps) wp] :
  wp (throw e : ExceptT ε m α) = PredTrans.throw e := by
    ext; simp[wp, throw, throwThe, MonadExceptOf.throw, ExceptT.mk, pure, PredTrans.pure, PredTrans.throw]

-- MonadExceptOf is not lifted via MonadLift (tryCatch) but rather via individual instances for StateT etc.
-- @[simp]
-- theorem MonadExceptOf.wp_throw [WP m msh] [WP n nsh] [MonadLift m n] [MonadLift (PredTrans msh) (PredTrans nsh)] [MonadExceptOf ε m] [WPMonadLift m n msh nsh] :
--   wp (MonadExceptOf.throw (ε:=ε) e : n α) = MonadLift.monadLift (wp (MonadExceptOf.throw (ε:=ε) e : m α)) := by
--     simp [MonadStateOf.set, liftM, monadLift]
