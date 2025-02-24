import MPL.Idd
import MPL.PredTrans

namespace MPL

class WP (m : Type → Type) (ps : outParam PredShape) where
  wp {α} (x : m α) : PredTrans ps α
  wp_mono {α} (x : m α) (Q₁ Q₂ : PostCond α ps) :
    Q₁ ≤ Q₂ → (wp x).apply Q₁ ≤ (wp x).apply Q₂

notation:max "wp⟦" x "⟧" => WP.wp x

@[simp]
theorem WP.wp_dite {c : Prop} [Decidable c] {t : c → m α} {e : ¬c → m α} [WP m ps] :
  wp⟦dite c t e⟧ = if h : c then wp⟦t h⟧ else wp⟦e h⟧ := by
    split <;> simp

@[simp]
theorem WP.wp_ite {c : Prop} [Decidable c] {t : m α} {e : m α} [WP m ps] :
  wp⟦ite c t e⟧ = if c then wp⟦t⟧ else wp⟦e⟧ := by
  split <;> simp

export WP (wp wp_mono wp_dite wp_ite)

end MPL
open MPL

instance Idd.instWP : WP Idd .pure where
  wp x := PredTrans.pure x.run
  wp_mono x _ _ h := h.1 x.run

theorem Idd.by_wp {prog : Idd α} (P : α → Prop) :
  (wp prog).apply (PostCond.total P) → P (Idd.run prog) := id

instance StateT.instWP [Monad m] [WP m ps] : WP (StateT σ m) (.arg σ ps) where
  wp x := { apply := fun Q s => (wp (x s)).apply (fun (a, s') => Q.1 a s', Q.2) }
  wp_mono {α} x Q₁ Q₂ h := by
    intro s
    simp only [wp]
    apply wp_mono (x s)
    simp only [Prod.mk_le_mk, h.2, and_true]
    intro x
    apply h.1

instance ReaderT.instWP [Monad m] [WP m ps] : WP (ReaderT ρ m) (.arg ρ ps) where
  wp x := { apply := fun Q r => (wp (x r)).apply (fun a => Q.1 a r, Q.2) }
  wp_mono x Q₁ Q₂ h := by
    intro r
    simp only [wp]
    apply wp_mono (x r)
    simp only [Prod.mk_le_mk, h.2, and_true]
    intro x
    apply h.1

instance ExceptT.instWP [Monad m] [WP m ps] : WP (ExceptT ε m) (.except ε ps) where
  wp x := { apply := fun Q => (wp (x.run)).apply (fun | .ok a => Q.1 a | .error e => Q.2.1 e, Q.2.2) }
  wp_mono x Q₁ Q₂ h := by
    simp [wp, bind, ExceptT.bind]
    apply wp_mono _ _ _ ?_
    simp[h.2.2]
    intro x
    cases x
    case error e => apply h.2.1 e
    case ok a => apply h.1 a

instance EStateM.instWP : WP (EStateM ε σ) (.except ε (.arg σ .pure)) where
  wp x := { apply := fun Q s => match x s with
    | .ok a s' => Q.1 a s'
    | .error e s' => Q.2.1 e s'
  }
  wp_mono x Q₁ Q₂ h := by
    intro s
    simp[wp]
    cases (x s) <;> apply_rules [h.1,h.2.1]
