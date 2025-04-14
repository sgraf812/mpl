import MPL.SPred

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

abbrev PreCond (ps : PredShape) : Type := SPred (PredShape.args ps)

@[ext]
theorem PreCond.ext {ps : PredShape} {P Q : PreCond (.arg σ ps)} : (∀ s, P s = Q s) → P = Q := SPred.ext

abbrev PreCond.pure {ps : PredShape} (P : Prop) : PreCond ps := ⌜P⌝
app_unexpand_rule PreCond.pure
  | `($_ $P) => ``(⌜$P⌝)

instance : Inhabited (PreCond ps) where
  default := PreCond.pure True

example {ρ ε σ : Type} : PreCond (.arg σ (.arg ρ (.except ε .pure))) = (σ → ρ → Prop) := rfl

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
