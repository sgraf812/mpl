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

theorem MonadFunctorT.monadMap_trans_apply [WP o ps] [MonadFunctor n o] [MonadFunctorT m n] :
  wp⟦MonadFunctorT.monadMap f x : o α⟧ Q = wp⟦MonadFunctor.monadMap (m:=n) (MonadFunctorT.monadMap (m:=m) f) x : o α⟧ Q := by
    simp only [MonadFunctorT.monadMap]

theorem MonadFunctorT.monadMap_refl_apply [WP m ps] :
  wp⟦MonadFunctorT.monadMap f x : m α⟧ Q = wp⟦f x : m α⟧ Q := by
    simp only [MonadFunctorT.monadMap]

theorem ReaderT.withReader_apply [WP m psm] :
  wp⟦MonadWithReaderOf.withReader f x : ReaderT ρ m α⟧ Q = fun r => wp⟦x⟧ (fun a _ => Q.1 a r, Q.2) (f r) := rfl

theorem MonadWithReaderOf.withReader_apply [MonadWithReaderOf ρ m] [WP n nsh] [MonadFunctor m n] (f : ρ → ρ) (x : n α) :
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
      WP.ExceptT_run_apply, WPMonad.bind_apply, WPMonad.wp_ite, WPMonad.wp_pure, PredTrans.ite_apply,
      PredTrans.pure_apply, MonadReader.read_apply, MonadReaderOf.read_apply,
      ExceptT.monadLift_apply, PredTrans.monadLiftExcept_apply, StateT.monadLift_apply,
      PredTrans.monadLiftArg_apply, ReaderT.read_apply]
    simp only [SVal.ite_app, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.ite_eq_false]

end MPL
