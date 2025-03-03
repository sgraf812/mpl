import MPL.Idd
import MPL.PredTrans

namespace MPL

class WP (m : Type → Type) (ps : outParam PredShape) where
  wp {α} (x : m α) : PredTrans ps α

notation:max "wp⟦" x "⟧" => WP.wp x

@[simp]
theorem WP.wp_dite {c : Prop} [Decidable c] {t : c → m α} {e : ¬c → m α} [WP m ps] :
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

instance Idd.instWP : WP Idd .pure where
  wp x := PredTrans.pure x.run

theorem Idd.by_wp {prog : Idd α} (P : α → Prop) :
  (wp prog).apply (PostCond.total P) → P (Idd.run prog) := id

theorem Id.by_wp {prog : Id α} (P : α → Prop) :
  (wp prog).apply (PostCond.total P) → P (Id.run prog) := id

instance StateT.instWP [Monad m] [WP m ps] : WP (StateT σ m) (.arg σ ps) where
  wp x :=
    { apply := fun Q s => (wp (x s)).apply (fun (a, s') => Q.1 a s', Q.2),
      mono := by
        intro _ _ h s
        simp only [wp]
        apply wp⟦x s⟧.mono
        simp only [Prod.mk_le_mk, h.2, and_true]
        intro x
        apply h.1 }

instance ReaderT.instWP [Monad m] [WP m ps] : WP (ReaderT ρ m) (.arg ρ ps) where
  wp x :=
    { apply := fun Q r => (wp (x r)).apply (fun a => Q.1 a r, Q.2),
      mono := by
        intro _ _ h r
        simp only [wp]
        apply wp⟦x r⟧.mono
        simp only [Prod.mk_le_mk, h.2, and_true]
        intro x
        apply h.1 }

instance ExceptT.instWP [Monad m] [WP m ps] : WP (ExceptT ε m) (.except ε ps) where
  wp x :=
    { apply := fun Q => (wp (x.run)).apply (fun | .ok a => Q.1 a | .error e => Q.2.1 e, Q.2.2),
      mono := by
        intro _ _ h
        apply wp⟦x.run⟧.mono _ _
        simp [wp, PredTrans.apply, bind, ExceptT.bind, h.2.2]
        intro x
        cases x
        case error e => apply h.2.1 e
        case ok a => apply h.1 }

instance EStateM.instWP : WP (EStateM ε σ) (.except ε (.arg σ .pure)) where
  wp x :=
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
