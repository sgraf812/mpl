import Lean
import MPL.Idd
import MPL.PredTrans

namespace MPL

class WP (m : Type → Type u) (ps : outParam PredShape) where
  wp {α} (x : m α) : PredTrans ps α

open Lean.Parser.Term in
syntax:max "wp⟦" term:min optType "⟧" : term
macro_rules
  | `(wp⟦$x:term⟧) => `(WP.wp $x)
  | `(wp⟦$x:term : $ty⟧) => `(WP.wp ($x : $ty))

-- σ₁ → ... → σₙ → Prop σᵢ
open Lean.PrettyPrinter in
@[app_unexpander WP.wp]
protected def unexpandWP : Unexpander
  | `($_ $x) => `(wp⟦$x⟧)
--  | `($_ ($x : $ty)) => `(wp⟦$x : $ty⟧) -- TODO?!
  | _ => (throw () : UnexpandM _)

variable {m : Type → Type u}

@[simp]
theorem WP.wp_dite {c : Prop} [Decidable c] {t : c → m α} {e : ¬ c → m α} [WP m ps] :
  wp⟦dite c t e⟧ = if h : c then wp⟦t h⟧ else wp⟦e h⟧ := by
    split <;> simp

@[simp]
theorem WP.wp_ite {c : Prop} [Decidable c] {t : m α} {e : m α} [WP m ps] :
  wp⟦ite c t e⟧ = if c then wp⟦t⟧ else wp⟦e⟧ := by
  split <;> simp

export WP (wp wp_dite wp_ite)

end MPL
open MPL

variable {m : Type → Type u}

instance Id.instWP : WP Id .pure where
  wp x := PredTrans.pure x.run

theorem Id.by_wp {α} {x : α} {prog : Id α} (h : x = Id.run prog) (P : α → Prop) :
  (wp prog).apply (PostCond.total P) → P x := h ▸ id

instance Idd.instWP : WP Idd .pure where
  wp x := PredTrans.pure x.run

theorem Idd.by_wp {α} {x : α} {prog : Idd α} (h : Idd.run prog = x) (P : α → Prop) :
  (wp prog).apply (PostCond.total P) → P x := h ▸ id

instance StateT.instWP [WP m ps] : WP (StateT σ m) (.arg σ ps) where
  wp x := PredTrans.pushArg (fun s => wp⟦x s⟧)

instance ReaderT.instWP [WP m ps] : WP (ReaderT ρ m) (.arg ρ ps) where
  wp x := PredTrans.pushArg (fun s => (·, s) <$> wp⟦x s⟧)

instance ExceptT.instWP [WP m ps] : WP (ExceptT ε m) (.except ε ps) where
  wp x := PredTrans.pushExcept wp⟦x⟧

-- def EStateM.Result.toExceptState {ε σ α} (x : EStateM.Result ε σ α) : Except ε α × σ :=
--   match x with
--   | .ok a s => (.ok a, s)
--   | .error e s => (.error e, s)

instance EStateM.instWP : WP (EStateM ε σ) (.except ε (.arg σ .pure)) where
  wp x := -- Could define as PredTrans.mkExcept (PredTrans.modifyGetM (fun s => pure (EStateM.Result.toExceptState (x s))))
    { apply := fun Q s => match x s with
        | .ok a s' => Q.1 a s'
        | .error e s' => Q.2.1 e s'
      mono := by
        intro _ _ h s
        simp[wp]
        cases (x s) <;> apply_rules [h.1,h.2.1]
    }

instance State.instWP : WP (StateM σ) (.arg σ .pure) := inferInstanceAs (WP (StateT σ Id) (.arg σ .pure))
instance Reader.instWP : WP (ReaderM ρ) (.arg ρ .pure) := inferInstanceAs (WP (ReaderT ρ Id) (.arg ρ .pure))
instance Except.instWP : WP (Except ε) (.except ε .pure) := inferInstanceAs (WP (ExceptT ε Id) (.except ε .pure))

@[simp]
theorem WP.popArg_StateT_wp [WP m ps] (x : StateT σ m α) :
  wp⟦x⟧.popArg s = wp⟦x.run s⟧ := by simp[wp, StateT.run]

@[simp]
theorem WP.popArg_ReaderT_wp [WP m ps] (x : ReaderT ρ m α) :
  wp⟦x⟧.popArg s = (·, s) <$> wp⟦x.run s⟧ := by simp[wp, ReaderT.run]

@[simp]
theorem WP.popExcept_ExceptT_wp [WP m ps] (x : ExceptT ε m α) :
  wp⟦x⟧.popExcept = wp⟦x.run⟧ := by simp[wp, ExceptT.run]

@[simp]
theorem WP.ReaderT_run_apply [WP m ps] (x : ReaderT ρ m α) :
  wp⟦x.run r⟧.apply Q = wp⟦x⟧.apply (fun a _ => Q.1 a, Q.2) r := rfl

@[simp]
theorem WP.StateT_run_apply [WP m ps] (x : StateT σ m α) :
  wp⟦x.run s⟧.apply Q = wp⟦x⟧.apply (fun a s => Q.1 (a, s), Q.2) s := rfl

@[simp]
theorem WP.ExceptT_run_apply [WP m ps] (x : ExceptT ε m α) :
  wp⟦x.run⟧.apply Q = wp⟦x⟧.apply (fun a => Q.1 (.ok a), fun e => Q.1 (.error e), Q.2) := by
    simp[wp, ExceptT.run]
    congr
    (ext x; cases x) <;> rfl

-- the following are just the definitions of wp:
-- @[simp] -- leads to errors in WPMonad
theorem WP.pushExcept_wp [WP m ps] (x : ExceptT ε m α) : PredTrans.pushExcept wp⟦x⟧ = wp⟦x⟧ := by simp[wp]
-- @[simp] -- leads to errors
theorem WP.pushArg_wp [WP m ps] (x : StateT σ m α) : PredTrans.pushArg (fun s => wp⟦x s⟧) = wp⟦x⟧ := by simp[wp]

def WP.dite_apply {ps} {Q : PostCond α ps} (c : Prop) [Decidable c] [WP m ps] (t : c → m α) (e : ¬ c → m α) :
  wp⟦if h : c then t h else e h⟧.apply Q = if h : c then wp⟦t h⟧.apply Q else wp⟦e h⟧.apply Q := by split <;> rfl

def WP.ite_apply {ps} {Q : PostCond α ps} (c : Prop) [Decidable c] [WP m ps] (t : m α) (e : m α) :
  wp⟦if c then t else e⟧.apply Q = if c then wp⟦t⟧.apply Q else wp⟦e⟧.apply Q := by split <;> rfl
