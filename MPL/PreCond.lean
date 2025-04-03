import MPL.SProp

namespace MPL

inductive PredShape : Type 1 where
  | pure : PredShape
  | arg : (σ : Type) → PredShape → PredShape
  | except : (ε : Type) → PredShape → PredShape

@[simp]
abbrev PredShape.args : PredShape → List Type
  | .pure => []
  | .arg σ s => σ :: PredShape.args s
  | .except ε s => PredShape.args s

@[simp]
abbrev PreCond (ps : PredShape) : Type := SProp (PredShape.args ps)

@[ext]
theorem PreCond.ext {ps : PredShape} {P Q : PreCond (.arg σ ps)} : (∀ s, P s = Q s) → P = Q := SProp.ext

abbrev PreCond.pure : {ps : PredShape} → Prop → PreCond ps := SProp.pure

instance : Inhabited (PreCond ps) where
  default := PreCond.pure True

example {ρ ε σ : Type} : PreCond (.arg σ (.arg ρ (.except ε .pure))) = (σ → ρ → Prop) := rfl

theorem PreCond.imp_pure_extract_l {ps} {P : Prop} {P' : PreCond ps} {Q : PreCond ps}
  (h : P → P' ⊢ₛ Q) : ⌜P⌝ ∧ P' ⊢ₛ Q := by
  induction ps
  case pure => intro ⟨hp, hp'⟩; exact h hp hp'
  case arg σ s ih => intro s; apply ih (fun hp => h hp s)
  case except ε s ih => simp; apply ih h

theorem PreCond.imp_pure_extract_r {ps} {P : Prop} {P' : PreCond ps} {Q : PreCond ps}
  (h : P → P' ⊢ₛ Q) : P' ∧ ⌜P⌝ ⊢ₛ Q := by
  induction ps
  case pure => intro ⟨hp, hp'⟩; exact h hp' hp
  case arg σ s ih => intro s; apply ih (fun hp => h hp s)
  case except ε s ih => simp; apply ih h

theorem PreCond.imp_pure_extract {ps} {P : Prop} {Q : PreCond ps}
  (h : P → ⌜True⌝ ⊢ₛ Q) : ⌜P⌝ ⊢ₛ Q := by
  induction ps
  case pure => intro hp; exact (h hp) .intro
  case arg σ s ih => intro s; apply ih (fun hp => h hp s)
  case except ε s ih => simp; apply ih h

@[simp]
theorem PreCond.entails_false {x : PreCond ps} : ⌜False⌝ ⊢ₛ x := by
  induction ps
  case pure => exact False.elim
  case arg σ s ih => intro; exact ih
  case except ε s ih => exact ih

@[simp]
theorem PreCond.entails_true {x : PreCond ps} : x ⊢ₛ ⌜True⌝ := by
  induction ps
  case pure => exact fun _ => True.intro
  case arg σ s ih => intro; exact ih
  case except ε s ih => exact ih
