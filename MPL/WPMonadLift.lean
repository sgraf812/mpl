import MPL.WPMonad

namespace MPL

-- TODO: Figure out whether the following instances are useful (I don't think they are.)
/-
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
  pure_pure x := by ext; simp only [monadLiftArg_apply, pure_apply]
  bind_bind x f := by ext Q σ; simp only [Bind.bind, bind, monadLiftArg_apply]

instance PredTrans.instLiftMonadMorphismDropFail : MonadMorphism (PredTrans ps) (PredTrans (.except ε ps)) MonadLift.monadLift where
  pure_pure x := by ext; simp only [monadLiftExcept_apply, pure_apply]
  bind_bind x f := by ext Q; simp only [Bind.bind, bind, monadLiftExcept_apply]
-/

class WPMonadLift (m : semiOutParam (Type → Type)) (n : Type → Type) (psm : outParam PredShape) (psn : outParam PredShape)
  [WP m psm] [WP n psn] [MonadLift m n] [MonadLift (PredTrans psm) (PredTrans psn)] where
  monadLift_apply {x : m α} {Q : PostCond α psn} :
    wp⟦MonadLift.monadLift x : n α⟧.apply Q = PredTrans.apply (MonadLift.monadLift wp⟦x⟧) Q

namespace WP
  export WPMonadLift (monadLift_apply)
end WP

instance StateT.instWPMonadLift [Monad m] [WP m psm] [LawfulMonad m] [MonadMorphism m (PredTrans psm) wp] : WPMonadLift m (StateT σ m) psm (.arg σ psm) where
  monadLift_apply := by intros; simp only [wp, MonadLift.monadLift, StateT.lift,
    bind_pure_comp, map_map, PredTrans.pushArg_apply]

instance ReaderT.instWPMonadLift [Monad m] [WP m psm] [LawfulMonad m] [MonadMorphism m (PredTrans psm) wp] : WPMonadLift m (ReaderT ρ m) psm (.arg ρ psm) where
  monadLift_apply := by intros; simp only [wp, MonadLift.monadLift, PredTrans.pushArg_apply,
    StateT.lift, bind_pure_comp]

instance ExceptT.instWPMonadLift [Monad m] [WP m psm] [LawfulMonad m] [MonadMorphism m (PredTrans psm) wp] : WPMonadLift m (ExceptT ε m) psm (.except ε psm) where
  monadLift_apply := by intros; simp only [wp, MonadLift.monadLift, ExceptT.lift, ExceptT.mk,
    map_map]

end MPL
open MPL

protected theorem ReaderT.wp_read [Monad m] [WP m psm] [MonadMorphism m (PredTrans psm) wp] :
  wp⟦MonadReaderOf.read : ReaderT ρ m ρ⟧ = PredTrans.get := by
    ext; simp only [wp, MonadReaderOf.read, ReaderT.read, pure_pure, pure, PredTrans.pure,
      PredTrans.pushArg_apply, PredTrans.map_apply, PredTrans.get]

theorem ReaderT.read_apply [Monad m] [WP m psm] [MonadMorphism m (PredTrans psm) wp] :
  wp⟦MonadReaderOf.read : ReaderT ρ m ρ⟧.apply Q = fun r => Q.1 r r  := by
    simp only [ReaderT.wp_read, PredTrans.get_apply]

theorem MonadReaderOf.read_apply [MonadReaderOf ρ m] [WP m msh] [WP n nsh] [MonadLift m n] [MonadLift (PredTrans msh) (PredTrans nsh)] [wp : WPMonadLift m n msh nsh] :
  wp⟦MonadReaderOf.read : n ρ⟧.apply Q = (MonadLift.monadLift (n:=PredTrans nsh) wp⟦MonadReader.read : m ρ⟧).apply Q := by
    simp only [read, liftM, monadLift, WP.monadLift_apply] -- TODO: Fix lifting MonadReaderOf instance

theorem MonadReaderOf.readThe_apply [MonadReaderOf ρ m] [WP m sh] :
  wp⟦readThe ρ : m ρ⟧.apply Q = wp⟦MonadReaderOf.read : m ρ⟧.apply Q := by
    simp only [readThe]

theorem MonadReader.read_apply [MonadReaderOf ρ m] [WP m sh] :
  wp⟦MonadReader.read : m ρ⟧.apply Q = wp⟦MonadReaderOf.read : m ρ⟧.apply Q := by
    simp only [read, MonadReaderOf.readThe_apply]

protected theorem StateT.wp_get [WP m psm] [Monad m] [MonadMorphism m (PredTrans psm) wp] :
  wp⟦MonadStateOf.get : StateT σ m σ⟧ = PredTrans.get := by
    ext; simp only [wp, MonadStateOf.get, StateT.get, pure_pure, pure, PredTrans.pure,
      PredTrans.pushArg_apply, PredTrans.get]

theorem StateT.get_apply [WP m psm] [Monad m] [MonadMorphism m (PredTrans psm) wp] :
  wp⟦MonadStateOf.get : StateT σ m σ⟧.apply Q = fun s => Q.1 s s := by
    simp only [StateT.wp_get, PredTrans.get_apply]

theorem MonadStateOf.get_apply [WP m msh] [WP n nsh] [MonadLift m n] [MonadLift (PredTrans msh) (PredTrans nsh)] [MonadStateOf σ m] [WPMonadLift m n msh nsh] :
  wp⟦MonadStateOf.get : n σ⟧.apply Q = PredTrans.apply (MonadLift.monadLift (wp⟦MonadStateOf.get : m σ⟧)) Q := by
    simp only [get, liftM, monadLift, WPMonadLift.monadLift_apply]

theorem MonadStateOf.getThe_apply [WP m sh] [MonadStateOf σ m] :
  wp⟦getThe σ : m σ⟧.apply Q = wp⟦MonadStateOf.get : m σ⟧.apply Q := rfl

theorem MonadState.get_apply [WP m sh] [MonadStateOf σ m] :
  wp⟦MonadState.get : m σ⟧.apply Q = wp⟦MonadStateOf.get : m σ⟧.apply Q := rfl

protected theorem StateT.wp_set [WP m sh] [Monad m] [MonadMorphism m _ wp] (x : σ) :
  wp⟦MonadStateOf.set x : StateT σ m PUnit⟧ = PredTrans.set x := by
    ext; simp only [wp, MonadState.set, set, StateT.set, pure_pure, pure, PredTrans.pure,
      PredTrans.pushArg_apply, PredTrans.set]

theorem StateT.set_apply [WP m sh] [Monad m] [MonadMorphism m _ wp] (x : σ) :
  wp⟦MonadStateOf.set x : StateT σ m PUnit⟧.apply Q = fun _ => Q.1 ⟨⟩ x := by
    simp only [StateT.wp_set, PredTrans.set_apply]

theorem MonadStateOf.set_apply [WP m msh] [WP n nsh] [MonadLift m n] [MonadLift (PredTrans msh) (PredTrans nsh)] [MonadStateOf σ m] [WPMonadLift m n msh nsh] :
  wp⟦MonadStateOf.set x : n PUnit⟧.apply Q = PredTrans.apply (MonadLift.monadLift (wp⟦MonadStateOf.set (σ:=σ) x : m PUnit⟧)) Q := by
    simp only [set, liftM, monadLift, WPMonadLift.monadLift_apply]

theorem MonadState.set_apply [WP m sh] [MonadStateOf σ m] :
  wp⟦MonadState.set x : m PUnit⟧.apply Q = wp⟦MonadStateOf.set x : m PUnit⟧.apply Q := rfl

protected theorem StateT.wp_modifyGet [WP m sh] [Monad m] [MonadMorphism m (PredTrans sh) wp]
  (f : σ → α × σ) :
  wp⟦MonadStateOf.modifyGet f : StateT σ m α⟧ = PredTrans.modifyGet f := by
    simp only [wp, MonadStateOf.modifyGet, StateT.modifyGet, pure_pure, pure, PredTrans.pure,
      PredTrans.modifyGet]

theorem StateT.modifyGet_apply [WP m sh] [Monad m] [MonadMorphism m (PredTrans sh) wp]
  (f : σ → α × σ) :
  wp⟦MonadStateOf.modifyGet f : StateT σ m α⟧.apply Q = fun s => Q.1 (f s).1 (f s).2 := by
    simp only [wp, MonadStateOf.modifyGet, StateT.modifyGet, pure_pure, pure, PredTrans.pure,
      PredTrans.pushArg_apply]

theorem MonadStateOf.modifyGet_apply [WP m msh] [WP n nsh] [MonadLift m n] [MonadLift (PredTrans msh) (PredTrans nsh)] [MonadStateOf σ m] [WPMonadLift m n msh nsh]
  (f : σ → α × σ) :
  wp⟦MonadStateOf.modifyGet f : n α⟧.apply Q = PredTrans.apply (MonadLift.monadLift (wp⟦MonadState.modifyGet f : m α⟧)) Q := by
    simp only [modifyGet, liftM, monadLift, WPMonadLift.monadLift_apply]

theorem MonadStateOf.modifyGetThe_apply [WP m sh] [MonadStateOf σ m] (f : σ → α × σ) :
  wp⟦modifyGetThe σ f : m α⟧.apply Q = wp⟦MonadStateOf.modifyGet f : m α⟧.apply Q := rfl

theorem MonadState.modifyGet_apply [WP m sh] [MonadStateOf σ m] (f : σ → α × σ) :
  wp⟦MonadState.modifyGet f : m α⟧.apply Q = wp⟦MonadStateOf.modifyGet f : m α⟧.apply Q := rfl

theorem MonadStateOf.modify_apply [WP m msh] [MonadStateOf σ m]
  (f : σ → σ) :
  wp⟦modify f : m PUnit⟧.apply Q = wp⟦MonadStateOf.modifyGet fun s => ((), f s) : m PUnit⟧.apply Q := rfl

theorem MonadStateOf.modifyThe_apply [WP m sh] [MonadStateOf σ m] (f : σ → σ) :
  wp⟦modifyThe σ f : m PUnit⟧.apply Q = wp⟦MonadStateOf.modifyGet fun s => ((), f s) : m PUnit⟧.apply Q := rfl

protected theorem ExceptT.wp_throw [Monad m] [WP m ps] [MonadMorphism m (PredTrans ps) wp] :
  wp⟦throw e : ExceptT ε m α⟧ = PredTrans.throw e := by
    ext; simp only [wp, throw, throwThe, MonadExceptOf.throw, mk, pure_pure, pure, PredTrans.pure,
      PredTrans.pushExcept_apply, PredTrans.throw]

theorem ExceptT.throw_apply [Monad m] [WP m ps] [MonadMorphism m (PredTrans ps) wp] :
  wp⟦throw e : ExceptT ε m α⟧.apply Q = Q.2.1 e := by
    simp only [ExceptT.wp_throw, PredTrans.throw_apply]

-- MonadExceptOf is not lifted via MonadLift (tryCatch) but rather via individual instances for StateT etc.
-- @[simp]
-- theorem MonadExceptOf.wp_throw [WP m msh] [WP n nsh] [MonadLift m n] [MonadLift (PredTrans msh) (PredTrans nsh)] [MonadExceptOf ε m] [WPMonadLift m n msh nsh] :
--   wp (MonadExceptOf.throw (ε:=ε) e : n α) = MonadLift.monadLift (wp (MonadExceptOf.throw (ε:=ε) e : m α)) := by
--     simp [MonadStateOf.set, liftM, monadLift]
