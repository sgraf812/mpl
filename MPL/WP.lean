import Lean
import MPL.Idd
import MPL.PredTrans

namespace MPL

#check MonadFunctor.monadMap
class WP (m : Type → Type) (ps : outParam PredShape) where
  wp {α} (x : m α) : PredTrans ps α
  wp_subst (P : m α → Prop) : wp x ≤ wp x' → P x' → P x
  wp_app (f : m α → m β) {x x' : m α} : wp x ≤ wp x' → wp (f x) ≤ wp (f x')

open Lean.Parser.Term in
syntax:max "wp⟦" term:min optType "⟧" : term
macro_rules
  | `(wp⟦$x:term⟧) => `(WP.wp $x)
  | `(wp⟦$x:term : $ty⟧) => `(WP.wp ($x : $ty))

open Lean.PrettyPrinter in
@[app_unexpander WP.wp]
protected def unexpandWP : Unexpander
  | `($_ $x) => `(wp⟦$x⟧)
--  | `($_ ($x : $ty)) => `(wp⟦$x : $ty⟧) -- TODO?!
  | _ => (throw () : UnexpandM _)

noncomputable def wp1 {m : Type → Type} [WP m ps] (f : m β → m β) : PredTrans ps β → PredTrans ps β := fun t =>
  sInf { t' | ∃ x, t ≤ wp⟦x⟧ ∧ t' = wp⟦f x⟧  }

notation "wp1⟦" x "⟧" => wp1 x

theorem wp1_spec {m : Type → Type} [WP m ps] (f : m β → m β) (x : m β) : wp1 (m:=m) f wp⟦x⟧ = wp⟦f x⟧ := by
  simp[wp1]
  apply le_antisymm
  · apply sInf_le
    use x
  · apply le_sInf
    intro t' ⟨x', ⟨hx, ht⟩⟩
    subst ht
    apply WP.wp_app _ hx

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

instance Id.instWP : WP Id .pure where
  wp x := PredTrans.pure x.run
  wp_subst := by
    intro _ x  x' P hwp hx'
    exact hwp (fun a => P a, ()) hx'
  wp_app := by
    intro _ _ f _ _ h Q
    exact h (fun x => Q.1 (f x), Q.2)

theorem Id.by_wp {α} {x : α} {prog : Id α} (h : x = Id.run prog) (P : α → Prop) :
  (wp prog).apply (PostCond.total P) → P x := h ▸ id

instance Idd.instWP : WP Idd .pure where
  wp x := PredTrans.pure x.run
  wp_subst := by
    intro _ x  x' P hwp hx'
    exact hwp (fun a => P (.mk a), ()) hx'
  wp_app := by
    intro _ _ f _ _ h Q
    exact h (fun x => Q.1 (f (.mk x)).run, Q.2)

theorem Idd.by_wp {α} {x : α} {prog : Idd α} (h : x = Idd.run prog) (P : α → Prop) :
  (wp prog).apply (PostCond.total P) → P x := h ▸ id

instance StateT.instWP [Monad m] [WP m ps] : WP (StateT σ m) (.arg σ ps) where
  wp x := PredTrans.pushArg (fun s => wp⟦x s⟧)
  wp_subst := by
    intro _ x  x' P hwp hx'
    simp at hwp
    suffices h : ∀s, P (x s) from h
    exact hwp (fun a => P (fun s => a, s), ()) hx'
  wp_app := by
    intro _ _ f x x' h Q
    intro s
    replace h : ∀s, wp⟦x s⟧ ≤ wp⟦x' s⟧ := fun s Q => h (fun a s => Q.1 (a, s), Q.2) s
    let F x s := wp⟦f x s⟧
    suffices h : F x ≤ F x' by apply h
    intro s Q
    have := h s (fun (a, s) => wp⟦f (pure a) s⟧.apply (fun (a, s) => Q.1 a s, Q.2), Q.2)
    simp at this
    have : (do let ⟨a, s⟩ ← wp⟦x s⟧; wp⟦f (pure a) s⟧).apply (fun (a, s) => Q.1 a s, Q.2) ≤ _ := this
    exact h (fun x s => wp⟦f (pure x) s⟧.apply (fun (a, s) => Q.1 a s, Q.2), Q.2)

instance ReaderT.instWP [Monad m] [WP m ps] : WP (ReaderT ρ m) (.arg ρ ps) where
  wp x := PredTrans.pushArg (fun s => (·, s) <$> wp⟦x s⟧)

instance ExceptT.instWP [Monad m] [WP m ps] : WP (ExceptT ε m) (.except ε ps) where
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
