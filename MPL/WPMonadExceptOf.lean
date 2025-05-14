/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
import MPL.WPMonad
import MPL.WPMonadLift
import MPL.WPMonadFunctor

/-!
# Weakest precondition transformers for `MonadExceptOf`

The definitions in this module define `wp_simp` lemmas for interpreting `throw`, `throwThe`,
`tryCatch`, etc.

This type class cannot be lifted through `MonadLift` or `MonadFunctor`, so there is one lemma per
`MonadExceptOf` operation and instance to lift through; the classic m*n instances problem.
-/

namespace MPL

universe u
variable {m : Type → Type u} {ps : PostShape}

theorem MonadExcept.throw_apply [MonadExceptOf ε m] [WP m ps] :
  wp⟦throw e : m α⟧ Q = wp⟦MonadExceptOf.throw e : m α⟧ Q := rfl

theorem MonadExcept.throwThe_apply [MonadExceptOf ε m] [WP m ps] :
  wp⟦throwThe ε e : m α⟧ Q = wp⟦MonadExceptOf.throw e : m α⟧ Q := rfl

theorem Except.throw_apply :
  wp⟦MonadExceptOf.throw e : Except ε α⟧ Q = Q.2.1 e := by
    simp only [wp, PredTrans.pure, Id.run, MonadExceptOf.throw, PredTrans.pushExcept_apply]

theorem ExceptT.throw_apply [Monad m] [WPMonad m ps] :
  wp⟦MonadExceptOf.throw e : ExceptT ε m α⟧ Q = Q.2.1 e := by
    simp only [wp, MonadExceptOf.throw, ExceptT.mk, pure_pure, pure, PredTrans.pure,
      PredTrans.pushExcept_apply]

theorem EStateM.throw_apply :
  wp⟦MonadExceptOf.throw e : EStateM ε σ α⟧ Q = Q.2.1 e := by
    simp only [wp, MonadExceptOf.throw, EStateM.throw]

theorem ReaderT.throw_apply [WP m sh] [Monad m] [MonadExceptOf ε m] :
  wp⟦MonadExceptOf.throw (ε:=ε) e : ReaderT ρ m α⟧ Q = wp⟦MonadLift.monadLift (MonadExceptOf.throw (ε:=ε) e : m α) : ReaderT ρ m α⟧ Q := rfl

theorem StateT.throw_apply [WP m sh] [Monad m] [MonadExceptOf ε m] :
  wp⟦MonadExceptOf.throw (ε:=ε) e : StateT ρ m α⟧ Q = wp⟦MonadLift.monadLift (MonadExceptOf.throw (ε:=ε) e : m α) : StateT ρ m α⟧ Q := rfl

-- The following lemma is structurally different to StateT and others because of weird definitions
-- for lifting throw
theorem ExceptT.lift_throw_apply [WP m sh] [Monad m] [MonadExceptOf ε m] :
  wp⟦MonadExceptOf.throw (ε:=ε) e : ExceptT ε' m α⟧ Q = wp⟦MonadExceptOf.throw (ε:=ε) e : m (Except ε' α)⟧ (fun | .ok a => Q.1 a | .error e => Q.2.1 e, Q.2.2) := by
    simp only [wp, MonadExceptOf.throw, throwThe, PredTrans.pushExcept_apply]
    congr
    ext x
    split <;> rfl

theorem MonadExcept.tryCatch_apply [MonadExceptOf ε m] [WP m ps] :
  wp⟦tryCatch x h : m α⟧ Q = wp⟦MonadExceptOf.tryCatch x h : m α⟧ Q := rfl

theorem MonadExcept.tryCatchThe_apply [MonadExceptOf ε m] [WP m ps] :
  wp⟦tryCatchThe ε x h : m α⟧ Q = wp⟦MonadExceptOf.tryCatch x h : m α⟧ Q := rfl

theorem Except.tryCatch_apply :
  wp⟦MonadExceptOf.tryCatch x h : Except ε α⟧ Q = wp⟦x⟧ (Q.1, fun e => wp⟦h e⟧ Q, Q.2.2) := by
    simp only [wp, PredTrans.pure, Id.run, MonadExceptOf.tryCatch, Except.tryCatch,
      PredTrans.pushExcept_apply]
    cases x <;> simp

theorem ExceptT.tryCatch_apply [Monad m] [WPMonad m ps] :
  wp⟦MonadExceptOf.tryCatch x h : ExceptT ε m α⟧ Q = wp⟦x⟧ (Q.1, fun e => wp⟦h e⟧ Q, Q.2.2) := by
    simp only [wp, MonadExceptOf.tryCatch, ExceptT.tryCatch, ExceptT.mk, bind_bind,
      PredTrans.pushExcept_apply, PredTrans.bind_apply]
    congr
    ext x
    split <;> simp

open EStateM.Backtrackable in
theorem EStateM.tryCatch_apply {ε σ δ α x h Q} [EStateM.Backtrackable δ σ]:
  wp⟦MonadExceptOf.tryCatch x h : EStateM ε σ α⟧ Q = fun s => wp⟦x⟧ (Q.1, fun e s' => wp⟦h e⟧ Q (restore s' (save s)), Q.2.2) s := by
    ext s;
    simp only [wp, MonadExceptOf.tryCatch, EStateM.tryCatch, bind_bind,
      PredTrans.pushExcept_apply, PredTrans.bind_apply]
    cases x s <;> simp

theorem ReaderT.tryCatch_apply [WP m sh] [Monad m] [MonadExceptOf ε m] :
  wp⟦MonadExceptOf.tryCatch (ε:=ε) x h : ReaderT ρ m α⟧ Q = fun r => wp⟦MonadExceptOf.tryCatch (ε:=ε) (x.run r) (fun e => (h e).run r) : m α⟧ (fun a => Q.1 a r, Q.2) := by
    simp only [wp, MonadExceptOf.tryCatch, tryCatchThe, PredTrans.pushArg_apply,
      PredTrans.map_apply, ReaderT.run]

theorem StateT.tryCatch_apply [WP m sh] [Monad m] [MonadExceptOf ε m] :
  wp⟦MonadExceptOf.tryCatch (ε:=ε) x h : StateT σ m α⟧ Q = fun s => wp⟦MonadExceptOf.tryCatch (ε:=ε) (x.run s) (fun e => (h e).run s) : m (α × σ)⟧ (fun as => Q.1 as.1 as.2, Q.2) := by
    simp only [wp, MonadExceptOf.tryCatch, tryCatchThe, PredTrans.pushArg_apply, StateT.run]

theorem ExceptT.lift_tryCatch_apply [WP m sh] [Monad m] [MonadExceptOf ε m] :
  wp⟦MonadExceptOf.tryCatch (ε:=ε) x h : ExceptT ε' m α⟧ Q = wp⟦MonadExceptOf.tryCatch (ε:=ε) x h : m (Except ε' α)⟧ (fun | .ok a => Q.1 a | .error e => Q.2.1 e, Q.2.2) := by
    simp only [wp, MonadExceptOf.tryCatch, tryCatchThe, PredTrans.pushExcept_apply, ExceptT.mk]
    congr
    ext x
    split <;> rfl

example :
  wp (m:= ReaderT Char (StateT Bool (ExceptT Nat Id))) (do set true; throw 42; set false; get) =
  wp (m:= ReaderT Char (StateT Bool (ExceptT Nat Id))) (do set true; throw 42; get) := by
    ext Q : 2
    simp only [WP.bind_apply, MonadState.get_apply, MonadStateOf.get_apply, ReaderT.monadLift_apply,
      PredTrans.monadLiftArg_apply, StateT.get_apply, MonadStateOf.set_apply, StateT.set_apply,
      MonadExcept.throw_apply, ReaderT.throw_apply, StateT.throw_apply, StateT.monadLift_apply,
      ExceptT.throw_apply]

example :
  wp (m:= ReaderT Char (StateT Bool (ExceptT Nat Id))) (do try { set true; throw 42 } catch _ => set false; get) =
  wp (m:= ReaderT Char (StateT Bool (ExceptT Nat Id))) (do set false; get) := by
    ext Q : 2
    simp only [MonadExcept.tryCatch_apply, ReaderT.tryCatch_apply, StateT.tryCatch_apply,
      ExceptT.tryCatch_apply, WP.StateT_run_apply, WP.ReaderT_run_apply, WP.bind_apply,
      MonadState.get_apply, MonadStateOf.get_apply, ReaderT.monadLift_apply,
      PredTrans.monadLiftArg_apply, StateT.get_apply, MonadStateOf.set_apply, StateT.set_apply,
      MonadExcept.throw_apply, ReaderT.throw_apply, StateT.throw_apply, StateT.monadLift_apply,
      ExceptT.throw_apply]
