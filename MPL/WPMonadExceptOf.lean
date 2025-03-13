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

protected theorem ExceptT.wp_throw [Monad m] [WP m ps] [MonadMorphism m (PredTrans ps) wp] :
  wp⟦MonadExceptOf.throw e : ExceptT ε m α⟧ = PredTrans.throw e := by
    ext; simp only [wp, throw, throwThe, MonadExceptOf.throw, ExceptT.mk, pure_pure, pure, PredTrans.pure,
      PredTrans.pushExcept_apply, PredTrans.throw]

theorem ExceptT.throw_apply [Monad m] [WP m ps] [MonadMorphism m (PredTrans ps) wp] :
  wp⟦MonadExceptOf.throw e : ExceptT ε m α⟧.apply Q = Q.2.1 e := by
    simp only [ExceptT.wp_throw, PredTrans.throw_apply]

theorem ReaderT.throw_apply [WP m sh] [Monad m] [WPMonad m sh] [MonadExceptOf ε m] :
  wp⟦MonadExceptOf.throw (ε:=ε) e : ReaderT ρ m α⟧.apply Q = PredTrans.apply (MonadLift.monadLift (wp⟦MonadExceptOf.throw (ε:=ε) e : m α⟧)) Q := by
    simp only [MonadExceptOf.throw, liftM, monadLift, WPMonadLift.monadLift_apply,
      PredTrans.monadLiftArg_apply, MonadExcept.throw_apply]

theorem StateT.throw_apply [WP m sh] [Monad m] [WPMonad m sh] [MonadExceptOf ε m] :
  wp⟦MonadExceptOf.throw (ε:=ε) e : StateT ρ m α⟧.apply Q = PredTrans.apply (MonadLift.monadLift (wp⟦MonadExceptOf.throw (ε:=ε) e : m α⟧)) Q := by
    simp only [MonadExceptOf.throw, liftM, monadLift, WPMonadLift.monadLift_apply,
      PredTrans.monadLiftArg_apply, MonadExcept.throwThe_apply, Function.comp_apply, StateT.lift_apply]

-- TODO: make instMonadExceptOfExceptT use ExceptT.lift instead of ExceptT.mk it for a simpler proof
theorem ExceptT.lift_throw_apply [WP m sh] [Monad m] [WPMonad m sh] [MonadExceptOf ε m] :
  wp⟦MonadExceptOf.throw (ε:=ε) e : ExceptT ε' m α⟧.apply Q = PredTrans.apply (MonadLift.monadLift (wp⟦MonadExceptOf.throw (ε:=ε) e : m α⟧)) Q := by
    simp only [MonadExceptOf.throw, liftM, monadLift, WPMonadLift.monadLift_apply,
      PredTrans.monadLiftExcept_apply, throwThe, ExceptT.lift_apply, ExceptT.lift, wp, PredTrans.pushExcept_apply, ExceptT.mk]
    sorry -- need to refactor instMonadExceptOfExceptT or show this property with a type class

theorem MonadExcept.tryCatch_apply [MonadExceptOf ε m] [WP m ps] :
  wp⟦tryCatch x h : m α⟧.apply Q = wp⟦MonadExceptOf.tryCatch x h : m α⟧.apply Q := rfl

theorem MonadExcept.tryCatchThe_apply [MonadExceptOf ε m] [WP m ps] :
  wp⟦tryCatchThe ε x h : m α⟧.apply Q = wp⟦MonadExceptOf.tryCatch x h : m α⟧.apply Q := rfl

protected theorem ExceptT.wp_tryCatch [Monad m] [WP m ps] [MonadMorphism m (PredTrans ps) wp] :
  wp⟦MonadExceptOf.tryCatch x h : ExceptT ε m α⟧ = PredTrans.tryCatch wp⟦x⟧ (fun e => wp⟦h e⟧) := by
    ext
    simp only [wp, MonadExceptOf.tryCatch, ExceptT.tryCatch, ExceptT.mk, bind_bind,
      PredTrans.pushExcept_apply, PredTrans.bind_apply, PredTrans.tryCatch]
    congr
    ext x
    split <;> simp

theorem ExceptT.tryCatch_apply [Monad m] [WP m ps] [MonadMorphism m (PredTrans ps) wp] :
  wp⟦MonadExceptOf.tryCatch x h : ExceptT ε m α⟧.apply Q = wp⟦x⟧.apply (Q.1, fun e => wp⟦h e⟧.apply Q, Q.2.2) := by
    simp only [ExceptT.wp_tryCatch, PredTrans.tryCatch]

theorem ReaderT.tryCatch_apply [WP m sh] [Monad m] [WPMonad m sh] [MonadExceptOf ε m] :
  wp⟦MonadExceptOf.tryCatch (ε:=ε) x h : ReaderT ρ m α⟧.apply Q = fun r => wp⟦MonadExceptOf.tryCatch (ε:=ε) (x.run r) (fun e => (h e).run r) : m α⟧.apply (fun a => Q.1 a r, Q.2) := by
    simp only [wp, MonadExceptOf.tryCatch, tryCatchThe, PredTrans.pushArg_apply,
      PredTrans.map_apply, ReaderT.run]

theorem StateT.tryCatch_apply [WP m sh] [Monad m] [WPMonad m sh] [MonadExceptOf ε m] :
  wp⟦MonadExceptOf.tryCatch (ε:=ε) x h : StateT σ m α⟧.apply Q = fun s => wp⟦MonadExceptOf.tryCatch (ε:=ε) (x.run s) (fun e => (h e).run s) : m (α × σ)⟧.apply (fun as => Q.1 as.1 as.2, Q.2) := by
    simp only [wp, MonadExceptOf.tryCatch, tryCatchThe, PredTrans.pushArg_apply, StateT.run]

theorem ExceptT.lift_tryCatch_apply [WP m sh] [Monad m] [WPMonad m sh] [MonadExceptOf ε m] :
  wp⟦MonadExceptOf.tryCatch (ε:=ε) x h : ExceptT ε' m α⟧.apply Q = wp⟦MonadExceptOf.tryCatch (ε:=ε) x h : m (Except ε' α)⟧.apply (fun | .ok a => Q.1 a | .error e => Q.2.1 e, Q.2.2) := by
    simp only [wp, MonadExceptOf.tryCatch, tryCatchThe, PredTrans.pushExcept_apply, ExceptT.mk]
    congr
    ext x
    split <;> rfl

example :
  wp (m:= ReaderT Char (StateT Bool (ExceptT Nat Id))) (do set true; throw 42; set false; get) =
  wp (m:= ReaderT Char (StateT Bool (ExceptT Nat Id))) (do set true; throw 42; get) := by
    ext Q : 2
    simp only [
      WP.popArg_wp, WP.popExcept_wp, WP.wp1_apply,
      WP.bind_apply, WP.StateT_run_apply, WP.ExceptT_run_apply,
      PredTrans.monadLiftArg_apply, PredTrans.monadLiftExcept_apply,
      WP.ite_apply, WP.pure_apply, PredTrans.ite_apply, PredTrans.pure_apply,
      StateT.set_apply, MonadStateOf.set_apply,
      StateT.get_apply, MonadStateOf.get_apply, MonadState.get_apply,
      MonadExcept.throw_apply,
      ExceptT.throw_apply, ReaderT.throw_apply, StateT.throw_apply, ExceptT.lift_throw_apply]

example :
  wp (m:= ReaderT Char (StateT Bool (ExceptT Nat Id))) (do try { set true; throw 42 } catch _ => set false; get) =
  wp (m:= ReaderT Char (StateT Bool (ExceptT Nat Id))) (do set false; get) := by
    ext Q : 2
    simp only [
      WP.popArg_wp, WP.popExcept_wp, WP.wp1_apply,
      WP.bind_apply, WP.ReaderT_run_apply, WP.StateT_run_apply, WP.ExceptT_run_apply,
      PredTrans.monadLiftArg_apply, PredTrans.monadLiftExcept_apply,
      WP.ite_apply, WP.pure_apply, PredTrans.ite_apply, PredTrans.pure_apply,
      StateT.set_apply, MonadStateOf.set_apply,
      StateT.get_apply, MonadStateOf.get_apply, MonadState.get_apply,
      MonadExcept.throw_apply,
      ExceptT.throw_apply, ReaderT.throw_apply, StateT.throw_apply, ExceptT.lift_throw_apply,
      MonadExcept.tryCatch_apply,
      ExceptT.tryCatch_apply, ReaderT.tryCatch_apply, StateT.tryCatch_apply, ExceptT.lift_tryCatch_apply]
