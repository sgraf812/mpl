/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
import MPL.WPMonad

/-!
# Weakest precondition transformers for `MonadLift`

The definitions in this module define `wp_simp` lemmas for interpreting `liftM` and thus the basis
for automatic reasoning about instances of `MonadStateOf`.
-/

namespace MPL

universe u
variable {m : Type → Type u} {ps : PostShape}

-- The next 3 instances are important to interpret away monadLift.
-- Note that we manage to map from `wp⟦·⟧ Q` to `wp⟦·⟧ (... Q ...)`
-- (modulo `fun s =>`) so that the next wp_simp rule immediately applies
theorem StateT.monadLift_apply [Monad m] [WPMonad m ps] (x : m α) (Q : PostCond α (.arg σ ps)) :
  wp⟦MonadLift.monadLift x : StateT σ m α⟧ Q = fun s => wp⟦x⟧ (fun a => Q.1 a s, Q.2) := by
    simp only [wp, MonadLift.monadLift, StateT.lift, bind_pure_comp, map_map,
      PredTrans.pushArg_apply, PredTrans.map_apply]

theorem ReaderT.monadLift_apply [Monad m] [WPMonad m ps] (x : m α) (Q : PostCond α (.arg ρ ps)) :
  wp⟦MonadLift.monadLift x : ReaderT ρ m α⟧ Q = fun s => wp⟦x⟧ (fun a => Q.1 a s, Q.2) := by
    simp only [wp, MonadLift.monadLift, PredTrans.pushArg_apply, PredTrans.map_apply]

theorem ExceptT.monadLift_apply [Monad m] [LawfulMonad m] [WPMonad m ps] (x : m α) (Q : PostCond α (.except ε ps)) :
  wp⟦MonadLift.monadLift x : ExceptT ε m α⟧ Q = wp⟦x⟧ (fun a => Q.1 a, Q.2.2) := by
    simp only [wp, MonadLift.monadLift, ExceptT.lift, ExceptT.mk, map_map,
      PredTrans.pushExcept_apply, PredTrans.map_apply]

theorem MonadLiftT.monadLift_trans_apply [WP o ps] [MonadLift n o] [MonadLiftT m n] :
  wp⟦MonadLiftT.monadLift x : o α⟧ Q = wp⟦MonadLift.monadLift (m:=n) (MonadLiftT.monadLift (m:=m) x) : o α⟧ Q := by
    simp only [MonadLiftT.monadLift]

theorem MonadLiftT.monadLift_refl_apply [WP m ps] :
  wp⟦MonadLiftT.monadLift x : m α⟧ Q = wp⟦x : m α⟧ Q := by
    simp only [MonadLiftT.monadLift]

-- The following instance is useful when we want to derive `modify f = monadLift (modify f)` and `modify f`
-- is defined in terms of multiple primitive definitions in `m` (`get`, `set`, ...), rather than just one call to `modifyGet`.
-- Example: `MonadStateOf.mkFreshNat_apply` in Tests/Toy.lean
-- The alternative would be to have one lemma for concrete transformer stack at which `mkFreshNat_apply` is used that simply unfolds the definition.
instance StateT.instLiftMonadMorphism [Monad m] [LawfulMonad m] : MonadMorphism m (StateT σ m) MonadLift.monadLift where
  pure_pure x := by ext; simp [liftM, MonadLift.monadLift, StateT.lift]
  bind_bind x f := by ext; simp [liftM, MonadLift.monadLift, StateT.lift]

instance ReaderT.instLiftMonadMorphism [Monad m] [LawfulMonad m] : MonadMorphism m (ReaderT ρ m) MonadLift.monadLift where
  pure_pure x := by ext; simp [liftM, MonadLift.monadLift, ReaderT.run, pure, ReaderT.pure]
  bind_bind x f := by ext; simp [liftM, MonadLift.monadLift, ReaderT.run, bind, ReaderT.bind]

instance ExceptT.instLiftMonadMorphism [Monad m] [LawfulMonad m] : MonadMorphism m (ExceptT ε m) MonadLift.monadLift where
  pure_pure x := by ext; simp only [MonadLift.monadLift, ExceptT.lift, map_pure, ExceptT.run_pure]; rfl
  bind_bind x f := by ext; simp [liftM, MonadLift.monadLift, ExceptT.lift, ExceptT.mk, bind, ExceptT.bind, ExceptT.bindCont]

-- Now rewrites for the standard lib:

theorem ReaderT.read_apply [Monad m] [WPMonad m psm] :
  wp⟦MonadReaderOf.read : ReaderT ρ m ρ⟧ Q = fun r => Q.1 r r  := by
    ext; simp only [wp, MonadReaderOf.read, ReaderT.read, pure_pure, pure, PredTrans.pure,
      PredTrans.pushArg_apply, PredTrans.map_apply]

theorem MonadReaderOf.read_apply [MonadReaderOf ρ m] [MonadLift m n] [WP n _] :
  wp⟦MonadReaderOf.read : n ρ⟧ Q = wp⟦MonadLift.monadLift (MonadReader.read : m ρ) : n ρ⟧ Q := rfl

theorem MonadReaderOf.readThe_apply [MonadReaderOf ρ m] [WP m sh] :
  wp⟦readThe ρ : m ρ⟧ Q = wp⟦MonadReaderOf.read : m ρ⟧ Q := by
    simp only [readThe]

theorem MonadReader.read_apply [MonadReaderOf ρ m] [WP m sh] :
  wp⟦MonadReader.read : m ρ⟧ Q = wp⟦MonadReaderOf.read : m ρ⟧ Q := by
    simp only [read, MonadReaderOf.readThe_apply]

theorem StateT.get_apply [Monad m] [WPMonad m psm] :
  wp⟦MonadStateOf.get : StateT σ m σ⟧ Q = fun s => Q.1 s s := by
    ext; simp only [wp, MonadStateOf.get, StateT.get, pure_pure, pure, PredTrans.pure,
      PredTrans.pushArg_apply]

theorem EStateM.get_apply :
    wp⟦MonadStateOf.get : EStateM ε σ σ⟧ Q = fun s => Q.1 s s := by
  ext; simp only [wp, MonadStateOf.get, EStateM.get]

theorem MonadStateOf.get_apply [MonadStateOf σ m] [MonadLift m n] [WP n _] :
  wp⟦MonadStateOf.get : n σ⟧ Q = wp⟦MonadLift.monadLift (MonadStateOf.get : m σ) : n σ⟧ Q := rfl

theorem MonadStateOf.getThe_apply [WP m sh] [MonadStateOf σ m] :
  wp⟦getThe σ : m σ⟧ Q = wp⟦MonadStateOf.get : m σ⟧ Q := rfl

theorem MonadState.get_apply [WP m sh] [MonadStateOf σ m] :
  wp⟦MonadState.get : m σ⟧ Q = wp⟦MonadStateOf.get : m σ⟧ Q := rfl

theorem StateT.set_apply [WP m sh] [Monad m] [MonadMorphism m _ wp] (x : σ) :
  wp⟦MonadStateOf.set x : StateT σ m PUnit⟧ Q = fun _ => Q.1 ⟨⟩ x := by
    ext; simp only [wp, MonadState.set, set, StateT.set, pure_pure, pure, PredTrans.pure,
      PredTrans.pushArg_apply]

theorem EStateM.set_apply (x : σ) :
    wp⟦MonadStateOf.set x : EStateM ε σ PUnit⟧ Q = fun _ => Q.1 ⟨⟩ x := by
  ext; simp only [wp, MonadState.set, set, EStateM.set, pure_pure, pure, PredTrans.pure,
    PredTrans.pushArg_apply]

theorem MonadStateOf.set_apply [MonadStateOf σ m] [MonadLift m n] [WP n _] :
  wp⟦MonadStateOf.set x : n PUnit⟧ Q = wp⟦MonadLift.monadLift (MonadStateOf.set (σ:=σ) x : m PUnit) : n PUnit⟧ Q := rfl

theorem MonadState.set_apply [WP m sh] [MonadStateOf σ m] :
  wp⟦MonadState.set x : m PUnit⟧ Q = wp⟦MonadStateOf.set x : m PUnit⟧ Q := rfl

theorem StateT.modifyGet_apply [WP m sh] [Monad m] [MonadMorphism m (PredTrans sh) wp]
  (f : σ → α × σ) :
  wp⟦MonadStateOf.modifyGet f : StateT σ m α⟧ Q = fun s => Q.1 (f s).1 (f s).2 := by
    simp only [wp, MonadStateOf.modifyGet, StateT.modifyGet, pure_pure, pure, PredTrans.pure,
      PredTrans.pushArg_apply]

theorem EStateM.modifyGet_apply (f : σ → α × σ) :
  wp⟦MonadStateOf.modifyGet f : EStateM ε σ α⟧ Q = fun s => Q.1 (f s).1 (f s).2 := by
      simp only [wp, MonadStateOf.modifyGet, EStateM.modifyGet, pure_pure, pure, PredTrans.pure,
      PredTrans.pushArg_apply]

theorem MonadStateOf.modifyGet_apply [MonadStateOf σ m] [MonadLift m n] [WP n _]
  (f : σ → α × σ) :
  wp⟦MonadStateOf.modifyGet f : n α⟧ Q = wp⟦MonadLift.monadLift (MonadState.modifyGet f : m α) : n α⟧ Q := rfl

theorem MonadStateOf.modifyGetThe_apply [WP m sh] [MonadStateOf σ m] (f : σ → α × σ) :
  wp⟦modifyGetThe σ f : m α⟧ Q = wp⟦MonadStateOf.modifyGet f : m α⟧ Q := rfl

theorem MonadState.modifyGet_apply [WP m sh] [MonadStateOf σ m] (f : σ → α × σ) :
  wp⟦MonadState.modifyGet f : m α⟧ Q = wp⟦MonadStateOf.modifyGet f : m α⟧ Q := rfl

theorem MonadStateOf.modify_apply [WP m msh] [MonadStateOf σ m]
  (f : σ → σ) :
  wp⟦modify f : m PUnit⟧ Q = wp⟦MonadStateOf.modifyGet fun s => ((), f s) : m PUnit⟧ Q := rfl

theorem MonadStateOf.modifyThe_apply [WP m sh] [MonadStateOf σ m] (f : σ → σ) :
  wp⟦modifyThe σ f : m PUnit⟧ Q = wp⟦MonadStateOf.modifyGet fun s => ((), f s) : m PUnit⟧ Q := rfl

theorem StateT.lift_apply [WP m sh] [Monad m] (x : m α) :
  wp⟦StateT.lift x : StateT σ m α⟧ Q = wp⟦MonadLift.monadLift x : StateT σ m α⟧ Q := rfl

theorem ExceptT.lift_apply [WP m sh] [Monad m] (x : m α) :
  wp⟦ExceptT.lift x : ExceptT ε m α⟧ Q = wp⟦MonadLift.monadLift x : ExceptT ε m α⟧ Q := rfl
