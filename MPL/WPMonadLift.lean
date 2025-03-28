import MPL.WPMonad

namespace MPL

universe u
variable {m : Type → Type u} {ps : PredShape}

-- The next 3 instances are important to interpret away monadLift.
-- Note that we manage to map from `wp⟦·⟧.apply Q` to `wp⟦·⟧.apply (... Q ...)`
-- (modulo `fun s =>`) so that the next wp_simp rule immediately applies
@[wp_simp]
theorem StateT.monadLift_apply [Monad m] [WPMonad m ps] (x : m α) (Q : PostCond α (.arg σ ps)) :
  wp⟦MonadLift.monadLift x : StateT σ m α⟧.apply Q = fun s => wp⟦x⟧.apply (fun a => Q.1 a s, Q.2) := by
    simp only [wp, MonadLift.monadLift, StateT.lift, bind_pure_comp, map_map,
      PredTrans.pushArg_apply, PredTrans.map_apply]

@[wp_simp]
theorem ReaderT.monadLift_apply [Monad m] [WPMonad m ps] (x : m α) (Q : PostCond α (.arg ρ ps)) :
  wp⟦MonadLift.monadLift x : ReaderT ρ m α⟧.apply Q = fun s => wp⟦x⟧.apply (fun a => Q.1 a s, Q.2) := by
    simp only [wp, MonadLift.monadLift, PredTrans.pushArg_apply, PredTrans.map_apply]

@[wp_simp]
theorem ExceptT.monadLift_apply [Monad m] [LawfulMonad m] [WPMonad m ps] (x : m α) (Q : PostCond α (.except ε ps)) :
  wp⟦MonadLift.monadLift x : ExceptT ε m α⟧.apply Q = wp⟦x⟧.apply (fun a => Q.1 a, Q.2.2) := by
    simp only [wp, MonadLift.monadLift, ExceptT.lift, ExceptT.mk, map_map,
      PredTrans.pushExcept_apply, PredTrans.map_apply]

@[wp_simp]
theorem MonadLiftT.monadLift_trans_apply [WP o ps] [MonadLift n o] [MonadLiftT m n] :
  wp⟦MonadLiftT.monadLift x : o α⟧.apply Q = wp⟦MonadLift.monadLift (m:=n) (MonadLiftT.monadLift (m:=m) x) : o α⟧.apply Q := rfl

@[wp_simp]
theorem MonadLiftT.monadLift_refl_apply [WP m ps] :
  wp⟦MonadLiftT.monadLift x : m α⟧.apply Q = wp⟦x : m α⟧.apply Q := rfl

derive_wp_simp liftM

-- The following instance is useful when we have want to derive `modify f = monadLift (modify f)` and `modify f`
-- is defined in terms of multiple primitive definitions in `m` (`get`, `set`, ...), rather than just one call to `modifyGet`.
-- Example: `MonadStateOf.mkFreshInt_apply`
-- The alternative would be to have one lemma for concrete transformer stack at which `mkFreshInt_apply` is used that simply unfolds the definition.
instance StateT.instLiftMonadMorphism [Monad m] [LawfulMonad m] : MonadMorphism m (StateT σ m) MonadLift.monadLift where
  pure_pure x := by ext; simp[liftM, MonadLift.monadLift, StateT.lift]
  bind_bind x f := by ext; simp[liftM, MonadLift.monadLift, StateT.lift]

instance ReaderT.instLiftMonadMorphism [Monad m] [LawfulMonad m] : MonadMorphism m (ReaderT ρ m) MonadLift.monadLift where
  pure_pure x := by ext; simp[liftM, MonadLift.monadLift, ReaderT.run, pure, ReaderT.pure]
  bind_bind x f := by ext; simp[liftM, MonadLift.monadLift, ReaderT.run, bind, ReaderT.bind]

instance ExceptT.instLiftMonadMorphism [Monad m] [LawfulMonad m] : MonadMorphism m (ExceptT ε m) MonadLift.monadLift where
  pure_pure x := by ext; simp[liftM, MonadLift.monadLift, ExceptT.lift]
  bind_bind x f := by ext; simp[liftM, MonadLift.monadLift, ExceptT.lift, ExceptT.mk, bind, ExceptT.bind, ExceptT.bindCont]

-- Now rewrites for the standard lib:

@[wp_simp]
theorem ReaderT.read_apply [Monad m] [WPMonad m psm] :
  wp⟦MonadReaderOf.read : ReaderT ρ m ρ⟧.apply Q = fun r => Q.1 r r  := by
    simp only [wp, MonadReaderOf.read, ReaderT.read, pure_pure, pure, PredTrans.pure,
      PredTrans.pushArg_apply, PredTrans.map_apply, PredTrans.get]

@[wp_simp]
theorem MonadReaderOf.read_apply [MonadReaderOf ρ m] [MonadLift m n] [WP n _] :
  wp⟦(instMonadReaderOfOfMonadLift (m:=m)).read : n ρ⟧.apply Q = wp⟦MonadLift.monadLift (MonadReader.read : m ρ) : n ρ⟧.apply Q := rfl

derive_wp_simp readThe
derive_wp_simp instMonadReaderOfOfMonadLift
derive_wp_simp instMonadReaderOfMonadReaderOf

@[wp_simp]
theorem MonadReaderOf.read_apply2 [MonadReaderOf ρ m] [MonadLift m n] [WP n _] :
  wp⟦MonadReaderOf.read : n ρ⟧.apply Q = wp⟦MonadLift.monadLift (MonadReader.read : m ρ) : n ρ⟧.apply Q := MonadReaderOf.read_apply

theorem MonadReader.read_apply [MonadReaderOf ρ m] [WP m sh] :
  wp⟦MonadReader.read : m ρ⟧.apply Q = wp⟦MonadReaderOf.read : m ρ⟧.apply Q := by
    simp only [read, readThe.wp_apply]

theorem StateT.get_apply [Monad m] [WPMonad m psm] :
  wp⟦MonadStateOf.get : StateT σ m σ⟧.apply Q = fun s => Q.1 s s := by
    simp only [wp, MonadStateOf.get, StateT.get, pure_pure, pure, PredTrans.pure,
      PredTrans.pushArg_apply, PredTrans.get]

theorem MonadStateOf.get_apply [MonadStateOf σ m] [MonadLift m n] [WP n _] :
  wp⟦MonadStateOf.get : n σ⟧.apply Q = wp⟦MonadLift.monadLift (MonadStateOf.get : m σ) : n σ⟧.apply Q := rfl

theorem MonadStateOf.getThe_apply [WP m sh] [MonadStateOf σ m] :
  wp⟦getThe σ : m σ⟧.apply Q = wp⟦MonadStateOf.get : m σ⟧.apply Q := rfl

theorem MonadState.get_apply [WP m sh] [MonadStateOf σ m] :
  wp⟦MonadState.get : m σ⟧.apply Q = wp⟦MonadStateOf.get : m σ⟧.apply Q := rfl

theorem StateT.set_apply [WP m sh] [Monad m] [MonadMorphism m _ wp] (x : σ) :
  wp⟦MonadStateOf.set x : StateT σ m PUnit⟧.apply Q = fun _ => Q.1 ⟨⟩ x := by
    simp only [wp, MonadState.set, set, StateT.set, pure_pure, pure, PredTrans.pure,
      PredTrans.pushArg_apply, PredTrans.set]

theorem MonadStateOf.set_apply [MonadStateOf σ m] [MonadLift m n] [WP n _] :
  wp⟦MonadStateOf.set x : n PUnit⟧.apply Q = wp⟦MonadLift.monadLift (MonadStateOf.set (σ:=σ) x : m PUnit) : n PUnit⟧.apply Q := rfl

theorem MonadState.set_apply [WP m sh] [MonadStateOf σ m] :
  wp⟦MonadState.set x : m PUnit⟧.apply Q = wp⟦MonadStateOf.set x : m PUnit⟧.apply Q := rfl

theorem StateT.modifyGet_apply [WP m sh] [Monad m] [MonadMorphism m (PredTrans sh) wp]
  (f : σ → α × σ) :
  wp⟦MonadStateOf.modifyGet f : StateT σ m α⟧.apply Q = fun s => Q.1 (f s).1 (f s).2 := by
    simp only [wp, MonadStateOf.modifyGet, StateT.modifyGet, pure_pure, pure, PredTrans.pure,
      PredTrans.pushArg_apply]

theorem MonadStateOf.modifyGet_apply [MonadStateOf σ m] [MonadLift m n] [WP n _]
  (f : σ → α × σ) :
  wp⟦MonadStateOf.modifyGet f : n α⟧.apply Q = wp⟦MonadLift.monadLift (MonadState.modifyGet f : m α) : n α⟧.apply Q := rfl

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
