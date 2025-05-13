/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
import MPL.WPMonad
import MPL.WPMonadLift

/-!
# Weakest precondition transformers for `MonadFunctor`

The definitions in this module define `wp_simp` lemmas for interpreting `mmap` and thus the basis
for automatic reasoning about instances of `MonadReaderWithOf`.
-/

namespace MPL

universe u
variable {m : Type → Type u} {ps : PostShape}

open MonadFunctor renaming monadMap → mmap

-- The following 3 instances exist for similar reasons as for instLiftMonadMorphism instances.
-- However, so far I was unable to find an example where they are useful.
-- Given the [MonadMorphism m m f] constraint, it is unlikely they actually are useful.
instance StateT.instMapMonadMorphism [Monad m] [MonadMorphism m m f] :
  MonadMorphism (StateT σ m) (StateT σ m) (mmap (m:=m) f) where
  pure_pure := by simp +unfoldPartialApp only [mmap, pure, StateT.pure, pure_pure, implies_true]
  bind_bind := by simp +unfoldPartialApp only [mmap, bind, StateT.bind, bind_bind, implies_true]

instance ReaderT.instMapMonadMorphism [Monad m] [MonadMorphism m m f] :
  MonadMorphism (ReaderT ρ m) (ReaderT ρ m) (mmap (m:=m) f) where
  pure_pure := by simp +unfoldPartialApp only [mmap, pure, ReaderT.pure, pure_pure, implies_true]
  bind_bind := by simp +unfoldPartialApp only [mmap, bind, ReaderT.bind, bind_bind, implies_true]

instance ExceptT.instMapMonadMorphism [Monad m] [MonadMorphism m m f] :
  MonadMorphism (ExceptT ε m) (ExceptT ε m) (mmap (m:=m) f) where
  pure_pure := by simp only [mmap, pure, ExceptT.pure, pure_pure, implies_true, ExceptT.mk]
  bind_bind := by
    intros
    simp +unfoldPartialApp only [mmap, bind, ExceptT.bind, bind_bind, implies_true, ExceptT.mk, ExceptT.bindCont]
    congr
    ext
    split <;> simp only [pure_pure]

-- The following 3 theorems are analogous to *.monadLift_apply.
-- We used to have a more tricky definition by rewriting to special monadMap defns on PredTrans, involving
--   wp1 : (∀ {α}, m α → m α) → PredTrans ps α → PredTrans ps α
-- that enjoys quite a tricky definition (see 9d0e89ec).
-- I found that relying on specialised lemmas is both much simpler and more reliable.
theorem StateT.monadMap_apply (m : Type → Type u) [Monad m] [WP m psm]
  (f : ∀{β}, m β → m β) {α} (x : StateT σ m α) (Q : PostCond α (.arg σ psm)) :
    wp⟦mmap (m:=m) f x⟧ Q = fun s => wp⟦f (x.run s)⟧ (fun (a, s) => Q.1 a s, Q.2) := by
  simp only [wp, MonadFunctor.monadMap, PredTrans.pushArg_apply, StateT.run]

theorem ReaderT.monadMap_apply (m : Type → Type u) [Monad m] [WP m psm]
  (f : ∀{β}, m β → m β) {α} (x : ReaderT ρ m α) (Q : PostCond α (.arg ρ psm)) :
    wp⟦mmap (m:=m) f x⟧ Q = fun s => wp⟦f (x.run s)⟧ (fun a => Q.1 a s, Q.2) := by
  simp only [wp, MonadFunctor.monadMap, PredTrans.pushArg_apply, PredTrans.map_apply, ReaderT.run]

theorem ExceptT.monadMap_apply (m : Type → Type u) [Monad m] [WP m psm]
  (f : ∀{β}, m β → m β) {α} (x : ExceptT ε m α) (Q : PostCond α (.except ε psm)) :
    wp⟦mmap (m:=m) f x⟧ Q = wp⟦f x.run⟧ (fun | .ok a => Q.1 a | .error e => Q.2.1 e, Q.2.2) := by
  simp only [wp, MonadFunctor.monadMap, PredTrans.pushExcept_apply, ExceptT.run]
  congr; ext; split <;> rfl

theorem ReaderT.withReader_apply [WP m psm] :
  wp⟦MonadWithReaderOf.withReader f x : ReaderT ρ m α⟧ Q = fun r => wp⟦x⟧ (fun a _ => Q.1 a r, Q.2) (f r) := rfl

theorem MonadWithReaderOf.withReader_apply [MonadWithReaderOf ρ m] [WP m msh] [WP n nsh] [MonadFunctor m n] [MonadFunctor (PredTrans msh) (PredTrans nsh)] (f : ρ → ρ) (x : n α) :
  wp⟦MonadWithReaderOf.withReader f x⟧ Q = wp⟦mmap (m:=m) (MonadWithReaderOf.withReader f) x⟧ Q := rfl

theorem MonadWithReaderOf.withTheReader_apply [MonadWithReaderOf ρ m] [WP m sh] (f : ρ → ρ) (x : m α) :
  wp⟦withTheReader ρ f x⟧ Q = wp⟦MonadWithReaderOf.withReader f x⟧ Q := rfl

theorem MonadWithReader.withReader_apply [MonadWithReaderOf ρ m] [WP m sh] (f : ρ → ρ) (x : m α) :
  wp⟦MonadWithReader.withReader f x⟧ Q = wp⟦MonadWithReaderOf.withReader f x⟧ Q := rfl

example :
  wp (m:= ExceptT Nat (StateT Nat (ReaderT Bool Id))) (withTheReader Bool not (do if (← read) then return 0 else return 1)) =
  wp (m:= ExceptT Nat (StateT Nat (ReaderT Bool Id))) (do if (← read) then return 1 else return 0) := by
    ext Q : 2
    simp only [MonadWithReaderOf.withTheReader_apply, MonadWithReaderOf.withReader_apply,
      ExceptT.monadMap_apply, StateT.monadMap_apply, ReaderT.withReader_apply, WP.StateT_run_apply,
      WP.ExceptT_run_apply, WP.bind_apply, MonadMorphism.ite_ite, pure_pure, PredTrans.ite_apply,
      PredTrans.pure_apply, MonadReader.read_apply, MonadReaderOf.read_apply,
      ExceptT.monadLift_apply, PredTrans.monadLiftExcept_apply, StateT.monadLift_apply,
      PredTrans.monadLiftArg_apply, ReaderT.read_apply]
    simp only [SVal.ite_app, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.ite_eq_false]

end MPL
