/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
import MPL.WPMonad
import MPL.WPMonadLift
import MPL.WPMonadFunctor

namespace MPL

universe u
variable {m : Type → Type u} {ps : PredShape}

theorem MonadExcept.throw_apply [MonadExceptOf ε m] [WP m ps] :
  wp⟦throw e : m α⟧.apply Q = wp⟦MonadExceptOf.throw e : m α⟧.apply Q := rfl

theorem MonadExcept.throwThe_apply [MonadExceptOf ε m] [WP m ps] :
  wp⟦throwThe ε e : m α⟧.apply Q = wp⟦MonadExceptOf.throw e : m α⟧.apply Q := rfl

theorem Except.throw_apply :
  wp⟦MonadExceptOf.throw e : Except ε α⟧.apply Q = Q.2.1 e := by
    simp only [wp, MonadExceptOf.throw, PredTrans.pushExcept_apply, PredTrans.throw, PredTrans.pure, Id.run, Except.error]

theorem ExceptT.throw_apply [Monad m] [WPMonad m ps] :
  wp⟦MonadExceptOf.throw e : ExceptT ε m α⟧.apply Q = Q.2.1 e := by
    simp only [wp, throw, throwThe, MonadExceptOf.throw, ExceptT.mk, pure_pure, pure, PredTrans.pure,
      PredTrans.pushExcept_apply, PredTrans.throw]

theorem ReaderT.throw_apply [WP m sh] [Monad m] [MonadExceptOf ε m] :
  wp⟦MonadExceptOf.throw (ε:=ε) e : ReaderT ρ m α⟧.apply Q = wp⟦MonadLift.monadLift (MonadExceptOf.throw (ε:=ε) e : m α) : ReaderT ρ m α⟧.apply Q := rfl

theorem StateT.throw_apply [WP m sh] [Monad m] [MonadExceptOf ε m] :
  wp⟦MonadExceptOf.throw (ε:=ε) e : StateT ρ m α⟧.apply Q = wp⟦MonadLift.monadLift (MonadExceptOf.throw (ε:=ε) e : m α) : StateT ρ m α⟧.apply Q := rfl

theorem ExceptT.lift_throw_apply [WP m sh] [Monad m] [MonadExceptOf ε m] :
  wp⟦MonadExceptOf.throw (ε:=ε) e : ExceptT ε' m α⟧.apply Q = wp⟦MonadExceptOf.throw (ε:=ε) e : m (Except ε' α)⟧.apply (fun | .ok a => Q.1 a | .error e => Q.2.1 e, Q.2.2) := by
    simp only [wp, MonadExceptOf.throw, throwThe, PredTrans.pushExcept_apply]
    congr
    ext x
    split <;> rfl

theorem MonadExcept.tryCatch_apply [MonadExceptOf ε m] [WP m ps] :
  wp⟦tryCatch x h : m α⟧.apply Q = wp⟦MonadExceptOf.tryCatch x h : m α⟧.apply Q := rfl

theorem MonadExcept.tryCatchThe_apply [MonadExceptOf ε m] [WP m ps] :
  wp⟦tryCatchThe ε x h : m α⟧.apply Q = wp⟦MonadExceptOf.tryCatch x h : m α⟧.apply Q := rfl

theorem Except.tryCatch_apply :
  wp⟦MonadExceptOf.tryCatch x h : Except ε α⟧.apply Q = wp⟦x⟧.apply (Q.1, fun e => wp⟦h e⟧.apply Q, Q.2.2) := by
    simp only [wp, PredTrans.pure, Id.run, MonadExceptOf.tryCatch, Except.tryCatch,
      PredTrans.pushExcept_apply]
    cases x <;> simp

theorem ExceptT.tryCatch_apply [Monad m] [WPMonad m ps] :
  wp⟦MonadExceptOf.tryCatch x h : ExceptT ε m α⟧.apply Q = wp⟦x⟧.apply (Q.1, fun e => wp⟦h e⟧.apply Q, Q.2.2) := by
    simp only [wp, MonadExceptOf.tryCatch, ExceptT.tryCatch, ExceptT.mk, bind_bind,
      PredTrans.pushExcept_apply, PredTrans.bind_apply, PredTrans.tryCatch]
    congr
    ext x
    split <;> simp

theorem ReaderT.tryCatch_apply [WP m sh] [Monad m] [MonadExceptOf ε m] :
  wp⟦MonadExceptOf.tryCatch (ε:=ε) x h : ReaderT ρ m α⟧.apply Q = fun r => wp⟦MonadExceptOf.tryCatch (ε:=ε) (x.run r) (fun e => (h e).run r) : m α⟧.apply (fun a => Q.1 a r, Q.2) := by
    simp only [wp, MonadExceptOf.tryCatch, tryCatchThe, PredTrans.pushArg_apply,
      PredTrans.map_apply, ReaderT.run]

theorem StateT.tryCatch_apply [WP m sh] [Monad m] [MonadExceptOf ε m] :
  wp⟦MonadExceptOf.tryCatch (ε:=ε) x h : StateT σ m α⟧.apply Q = fun s => wp⟦MonadExceptOf.tryCatch (ε:=ε) (x.run s) (fun e => (h e).run s) : m (α × σ)⟧.apply (fun as => Q.1 as.1 as.2, Q.2) := by
    simp only [wp, MonadExceptOf.tryCatch, tryCatchThe, PredTrans.pushArg_apply, StateT.run]

theorem ExceptT.lift_tryCatch_apply [WP m sh] [Monad m] [MonadExceptOf ε m] :
  wp⟦MonadExceptOf.tryCatch (ε:=ε) x h : ExceptT ε' m α⟧.apply Q = wp⟦MonadExceptOf.tryCatch (ε:=ε) x h : m (Except ε' α)⟧.apply (fun | .ok a => Q.1 a | .error e => Q.2.1 e, Q.2.2) := by
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
