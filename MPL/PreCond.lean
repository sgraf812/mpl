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

@[simp]
abbrev PreCond.pure : {ps : PredShape} → Prop → PreCond ps := SProp.pure

instance : Inhabited (PreCond ps) where
  default := PreCond.pure True

example {ρ ε σ : Type} : PreCond (.arg σ (.arg ρ (.except ε .pure))) = (σ → ρ → Prop) := rfl

-- noncomputable instance PreCond.instLattice : {ps : PredShape} → CompleteLattice (PreCond ps)
--   | .pure => ((inferInstance : CompleteLattice Prop) : CompleteLattice (PreCond .pure))
--   | .arg σ s => let _ := @instLattice s; (inferInstance : CompleteLattice (σ → PreCond s))
--   | .except ε s => @instLattice s
--
-- noncomputable instance PreCond.instPreorder {ps : PredShape} : Preorder (PreCond ps) := inferInstance
-- noncomputable instance PreCond.instLE {ps : PredShape} : LE (PreCond ps) := inferInstance
-- noncomputable instance PreCond.instTop {ps : PredShape} : Top (PreCond ps) := inferInstance
-- noncomputable instance PreCond.instBot {ps : PredShape} : Bot (PreCond ps) := inferInstance

theorem PreCond.imp_pure_extract_l {ps} {P : Prop} {P' : PreCond ps} {Q : PreCond ps}
  (h : P → SProp.entails P' Q) : SProp.entails sprop(⌜P⌝ ∧ P') Q := by
  induction ps
  case pure => intro ⟨hp, hp'⟩; exact h hp hp'
  case arg σ s ih => intro s; apply ih (fun hp => h hp s)
  case except ε s ih => simp; apply ih h

theorem PreCond.imp_pure_extract_r {ps} {P : Prop} {P' : PreCond ps} {Q : PreCond ps}
  (h : P → SProp.entails P' Q) : SProp.entails (sprop(P' ∧ ⌜P⌝)) Q := by
  induction ps
  case pure => intro ⟨hp, hp'⟩; exact h hp' hp
  case arg σ s ih => intro s; apply ih (fun hp => h hp s)
  case except ε s ih => simp; apply ih h

theorem PreCond.imp_pure_extract {ps} {P : Prop} {Q : PreCond ps}
  (h : P → SProp.entails sprop(⌜True⌝) Q) : SProp.entails sprop(⌜P⌝) Q := by
  induction ps
  case pure => intro hp; exact (h hp) .intro
  case arg σ s ih => intro s; apply ih (fun hp => h hp s)
  case except ε s ih => simp; apply ih h

@[simp]
theorem PreCond.entails_false {x : PreCond ps} : SProp.entails sprop(⌜False⌝) x := by
  induction ps
  case pure => exact False.elim
  case arg σ s ih => intro; exact ih
  case except ε s ih => exact ih

@[simp]
theorem PreCond.entails_true {x : PreCond ps} : SProp.entails x sprop(⌜True⌝) := by
  induction ps
  case pure => exact fun _ => True.intro
  case arg σ s ih => intro; exact ih
  case except ε s ih => exact ih
