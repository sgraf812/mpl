import MPL.WPMonad

namespace MPL

universe u
variable {m : Type → Type u} {ps : PredShape}

-- The following instance is useful when we have for example `monadLift (modify f : m α)` and `modify f`
-- is defined in terms of more primitive definitions in `m` (`get`, `set`, ...).
-- Example: `MonadStateOf.mkFreshInt_apply`
instance StateT.instLiftMonadMorphism [Monad m] [LawfulMonad m] : MonadMorphism m (StateT σ m) MonadLift.monadLift where
  pure_pure x := by ext; simp[liftM, MonadLift.monadLift, StateT.lift]
  bind_bind x f := by ext; simp[liftM, MonadLift.monadLift, StateT.lift]

instance ReaderT.instLiftMonadMorphism [Monad m] [LawfulMonad m] : MonadMorphism m (ReaderT ρ m) MonadLift.monadLift where
  pure_pure x := by ext; simp[liftM, MonadLift.monadLift, ReaderT.run, pure, ReaderT.pure]
  bind_bind x f := by ext; simp[liftM, MonadLift.monadLift, ReaderT.run, bind, ReaderT.bind]

instance ExceptT.instLiftMonadMorphism [Monad m] [LawfulMonad m] : MonadMorphism m (ExceptT ε m) MonadLift.monadLift where
  pure_pure x := by ext; simp[liftM, MonadLift.monadLift, ExceptT.lift]
  bind_bind x f := by ext; simp[liftM, MonadLift.monadLift, ExceptT.lift, ExceptT.mk, bind, ExceptT.bind, ExceptT.bindCont]

-- TODO: Figure out whether the following instances are useful (I don't think they are.)
/-
instance PredTrans.instLiftMonadMorphismArg : MonadMorphism (PredTrans ps) (PredTrans (.arg σ ps)) MonadLift.monadLift where
  pure_pure x := by ext; simp only [monadLiftArg_apply, pure_apply]
  bind_bind x f := by ext Q σ; simp only [Bind.bind, bind, monadLiftArg_apply]

instance PredTrans.instLiftMonadMorphismDropFail : MonadMorphism (PredTrans ps) (PredTrans (.except ε ps)) MonadLift.monadLift where
  pure_pure x := by ext; simp only [monadLiftExcept_apply, pure_apply]
  bind_bind x f := by ext Q; simp only [Bind.bind, bind, monadLiftExcept_apply]
-/

theorem WP.monadLift_pure_apply [WP m psm] [WP n psn] [Monad m] [Monad n] [MonadLift m n] [MonadMorphism m n MonadLift.monadLift]
  (a : α) (Q : PostCond α psn) :
  wp⟦MonadLift.monadLift (m:=m) (pure a) : n α⟧.apply Q = wp⟦pure a : n α⟧.apply Q := by
    simp only [pure_pure]

theorem WP.monadLift_bind_apply [WP m psm] [WP n psn] [Monad m] [Monad n] [MonadLift m n] [MonadMorphism m n MonadLift.monadLift]
  (x : m α) (f : α → m β) (Q : PostCond β psn) :
  wp⟦MonadLift.monadLift (m:=m) (x >>= f) : n β⟧.apply Q = wp⟦MonadLift.monadLift (m:=m) x >>= fun a => MonadLift.monadLift (m:=m) (f a) : n β⟧.apply Q := by
    simp only [bind_bind]

theorem WP.monadLift_map_apply [WP m psm] [WP n psn] [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n] [MonadLift m n] [MonadMorphism m n MonadLift.monadLift]
  (f : α → β) (x : m α) (Q : PostCond β psn) :
  wp⟦MonadLift.monadLift (m:=m) (f <$> x) : n β⟧.apply Q = wp⟦f <$> MonadLift.monadLift (m:=m) x : n β⟧.apply Q := by
    simp[map_map]

theorem WP.monadLift_seq_apply [WP m psm] [WP n psn] [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n] [MonadLift m n] [MonadMorphism m n MonadLift.monadLift]
  (f : m (α → β)) (x : m α) (Q : PostCond β psn) :
  wp⟦MonadLift.monadLift (m:=m) (f <*> x) : n β⟧.apply Q = wp⟦MonadLift.monadLift (m:=m) f <*> MonadLift.monadLift (m:=m) x : n β⟧.apply Q := by
    simp[seq_seq]

-- TODO: Reconsider whether we want this as a type class. It seems better to only apply monadLift_apply when we can also reduce the monadLift in PredTrans.
class WPMonadLift (m : semiOutParam (Type → Type u)) (n : Type → Type v) (psm : outParam PredShape) (psn : outParam PredShape)
  [WP m psm] [WP n psn] [MonadLift m n] [MonadLift (PredTrans psm) (PredTrans psn)] where
  monadLift_apply {x : m α} {Q : PostCond α psn} :
    wp⟦MonadLift.monadLift x : n α⟧.apply Q = PredTrans.apply (MonadLift.monadLift wp⟦x⟧) Q

namespace WP
  export WPMonadLift (monadLift_apply)
end WP

instance StateT.instWPMonadLift [Monad m] [WP m psm] [WPMonad m psm] : WPMonadLift m (StateT σ m) psm (.arg σ psm) where
  monadLift_apply := by intros; simp only [wp, MonadLift.monadLift, StateT.lift,
    bind_bind, pure_pure, PredTrans.pushArg_apply]

instance ReaderT.instWPMonadLift [WP m psm] : WPMonadLift m (ReaderT ρ m) psm (.arg ρ psm) where
  monadLift_apply := by intros; simp only [wp, MonadLift.monadLift, PredTrans.pushArg_apply,
    StateT.lift, bind_pure_comp]

instance ExceptT.instWPMonadLift [Monad m] [WP m psm] [LawfulMonad m] [WPMonad m psm] : WPMonadLift m (ExceptT ε m) psm (.except ε psm) where
  monadLift_apply := by intros; simp only [wp, MonadLift.monadLift, ExceptT.lift, ExceptT.mk,
    map_map]

end MPL
open MPL

theorem MonadLiftT.monadLift_trans_apply [WP o ps] [MonadLift n o] [MonadLiftT m n] :
  wp⟦MonadLiftT.monadLift x : o α⟧.apply Q = wp⟦MonadLift.monadLift (m:=n) (MonadLiftT.monadLift (m:=m) x) : o α⟧.apply Q := by
    simp only [MonadLiftT.monadLift]

theorem MonadLiftT.monadLift_refl_apply [WP m ps] :
  wp⟦MonadLiftT.monadLift x : m α⟧.apply Q = wp⟦x : m α⟧.apply Q := by
    simp only [MonadLiftT.monadLift]

protected theorem ReaderT.wp_read [Monad m] [WP m psm] [WPMonad m psm] :
  wp⟦MonadReaderOf.read : ReaderT ρ m ρ⟧ = PredTrans.get := by
    ext; simp only [wp, MonadReaderOf.read, ReaderT.read, pure_pure, pure, PredTrans.pure,
      PredTrans.pushArg_apply, PredTrans.map_apply, PredTrans.get]

theorem ReaderT.read_apply [Monad m] [WP m psm] [WPMonad m psm] :
  wp⟦MonadReaderOf.read : ReaderT ρ m ρ⟧.apply Q = fun r => Q.1 r r  := by
    simp only [ReaderT.wp_read, PredTrans.get_apply]

theorem MonadReaderOf.read_apply [MonadReaderOf ρ m] [WP m msh] [WP n nsh] [MonadLift m n] [MonadLift (PredTrans msh) (PredTrans nsh)] [wp : WPMonadLift m n msh nsh] :
  wp⟦MonadReaderOf.read : n ρ⟧.apply Q = (MonadLift.monadLift (n:=PredTrans nsh) wp⟦MonadReader.read : m ρ⟧).apply Q := by
    simp only [read, liftM, monadLift, WP.monadLift_apply]

theorem MonadReaderOf.readThe_apply [MonadReaderOf ρ m] [WP m sh] :
  wp⟦readThe ρ : m ρ⟧.apply Q = wp⟦MonadReaderOf.read : m ρ⟧.apply Q := by
    simp only [readThe]

theorem MonadReader.read_apply [MonadReaderOf ρ m] [WP m sh] :
  wp⟦MonadReader.read : m ρ⟧.apply Q = wp⟦MonadReaderOf.read : m ρ⟧.apply Q := by
    simp only [read, MonadReaderOf.readThe_apply]

protected theorem StateT.wp_get [WP m psm] [Monad m] [WPMonad m psm] :
  wp⟦MonadStateOf.get : StateT σ m σ⟧ = PredTrans.get := by
    ext; simp only [wp, MonadStateOf.get, StateT.get, pure_pure, pure, PredTrans.pure,
      PredTrans.pushArg_apply, PredTrans.get]

theorem StateT.get_apply [WP m psm] [Monad m] [WPMonad m psm] :
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

theorem StateT.lift_apply [WP m sh] [Monad m] (x : m α) :
  wp⟦StateT.lift x : StateT σ m α⟧.apply Q = wp⟦MonadLift.monadLift x : StateT σ m α⟧.apply Q := rfl

theorem ExceptT.lift_apply [WP m sh] [Monad m] (x : m α) :
  wp⟦ExceptT.lift x : ExceptT ε m α⟧.apply Q = wp⟦MonadLift.monadLift x : ExceptT ε m α⟧.apply Q := rfl
