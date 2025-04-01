import MPL.PreCond

namespace MPL

def FailConds : PredShape → Type
  | .pure => Unit
  | .arg _ s => FailConds s
  | .except ε s => (ε → PreCond s) × FailConds s

abbrev FailConds.const {ps : PredShape} (p : Prop) : FailConds ps := match ps with
  | .pure => ()
  | .arg σ s => @FailConds.const s p
  | .except ε s => (fun _ε => PreCond.pure p, @FailConds.const s p)

def FailConds.true : FailConds ps := FailConds.const True
def FailConds.false : FailConds ps := FailConds.const False

instance : Inhabited (FailConds ps) where
  default := FailConds.true

def FailConds.entails {ps : PredShape} (x y : FailConds ps) : Prop :=
  match ps with
  | .pure => True
  | .arg _ ps => @entails ps x y
  | .except _ ps => (∀ e, SProp.entails (x.1 e) (y.1 e)) ∧ @entails ps x.2 y.2

@[simp, refl]
theorem FailConds.entails_refl {ps : PredShape} (x : FailConds ps) : FailConds.entails x x := by
  induction ps
  case pure => simp[entails]
  case arg σ s ih => exact (ih x)
  case except ε s ih => simp only [entails, PreCond, SProp.entails_refl, implies_true, ih,
    and_self]

@[simp]
theorem FailConds.pure_def {x : FailConds .pure} : x = () := rfl

@[simp]
theorem FailConds.entails_false {x : FailConds ps} : FailConds.entails FailConds.false x := by
  simp only [false]
  induction ps
  case pure => simp[entails]
  case arg σ s ih => exact ih
  case except ε s ih => simp only [entails, PreCond.entails_false, implies_true, ih, and_self]

@[simp]
theorem FailConds.entails_true {x : FailConds ps} : FailConds.entails x FailConds.true := by
  simp only [true]
  induction ps
  case pure => simp[entails]
  case arg σ s ih => exact ih
  case except ε s ih => simp only [entails, PreCond.entails_true, implies_true, ih, and_self]

/-- A multi-barreled postcondition for the given predicate shape.
```
example : PostCond α (.arg ρ .pure) = ((α → ρ → Prop) × Unit) := rfl
example : PostCond α (.except ε .pure) = ((α → Prop) × (ε → Prop) × Unit) := rfl
example : PostCond α (.arg σ (.except ε .pure)) = ((α → σ → Prop) × (ε → Prop) × Unit) := rfl
example : PostCond α (.except ε (.arg σ .pure)) = ((α → σ → Prop) × (ε → σ → Prop) × Unit) := rfl
```
-/
abbrev PostCond (α : Type) (s : PredShape) : Type :=
  (α → PreCond s) × FailConds s

/-- A postcondition expressing total correctness. -/
abbrev PostCond.total (p : α → PreCond ps) : PostCond α ps :=
  (p, FailConds.false)

/-- A postcondition expressing partial correctness. -/
abbrev PostCond.partial (p : α → PreCond ps) : PostCond α ps :=
  (p, FailConds.true)

instance : Inhabited (PostCond α ps) where
  default := PostCond.total (fun _ => default)

@[simp]
abbrev PostCond.entails (p q : PostCond α ps) : Prop :=
  (∀ a, SProp.entails (p.1 a) (q.1 a)) ∧ FailConds.entails p.2 q.2

@[refl,simp]
abbrev PostCond.entails_refl (Q : PostCond α ps) : PostCond.entails Q Q := by
  simp only [entails, PreCond, SProp.entails_refl, implies_true, FailConds.entails_refl, and_self]

@[simp]
theorem PostCond.total_def {p : α → PreCond ps} : (p, FailConds.false) = PostCond.total p := rfl

@[simp]
theorem PostCond.partial_def {p : α → PreCond ps} : (p, FailConds.true) = PostCond.partial p := rfl

@[simp]
theorem PostCond.entails_total (p : α → PreCond ps) (q : PostCond α ps) : (PostCond.total p).entails q ↔ ∀ a, SProp.entails (p a) (q.1 a) := by
  simp only [total, entails, FailConds.entails_false, and_true]

@[simp]
theorem PostCond.entails_partial (p : PostCond α ps) (q : α → PreCond ps) : p.entails (PostCond.partial q) ↔ ∀ a, SProp.entails (p.1 a) (q a) := by
  simp only [total, entails, FailConds.entails_true, and_true]
