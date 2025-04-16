import MPL.PreCond
import MPL.Utils.UnexpandRule

namespace MPL

def FailConds : PredShape → Type
  | .pure => Unit
  | .arg _ s => FailConds s
  | .except ε s => (ε → PreCond s) × FailConds s

abbrev FailConds.const {ps : PredShape} (p : Prop) : FailConds ps := match ps with
  | .pure => ()
  | .arg σ s => @FailConds.const s p
  | .except ε s => (fun _ε => spred(⌜p⌝), @FailConds.const s p)

def FailConds.true : FailConds ps := FailConds.const True
def FailConds.false : FailConds ps := FailConds.const False

instance : Inhabited (FailConds ps) where
  default := FailConds.true

def FailConds.entails {ps : PredShape} (x y : FailConds ps) : Prop :=
  match ps with
  | .pure => True
  | .arg _ ps => @entails ps x y
  | .except _ ps => (∀ e, x.1 e ⊢ₛ y.1 e) ∧ @entails ps x.2 y.2

infixr:25 "⊢ₑ" => FailConds.entails

@[simp, refl]
theorem FailConds.entails_refl {ps : PredShape} (x : FailConds ps) : x ⊢ₑ x := by
  induction ps
  case pure => simp[entails]
  case arg σ s ih => exact (ih x)
  case except ε s ih => simp only [entails, PreCond, SPred.entails.refl, implies_true, ih,
    and_self]

@[simp]
theorem FailConds.pure_def {x : FailConds .pure} : x = () := rfl

@[simp]
theorem FailConds.entails_false {x : FailConds ps} : FailConds.false ⊢ₑ x := by
  simp only [false]
  induction ps
  case pure => simp[entails]
  case arg σ s ih => exact ih
  case except ε s ih => simp only [entails, PreCond.entails_false, implies_true, ih, and_self]

@[simp]
theorem FailConds.entails_true {x : FailConds ps} : x ⊢ₑ FailConds.true := by
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

open Lean Parser Term in
def funArrow : Parser := unicodeSymbol " ↦ " " => "
@[inherit_doc PostCond.total]
macro "⇓" xs:Lean.Parser.Term.funBinder+ funArrow e:term : term =>
  `(PostCond.total (fun $xs* => spred($e)))
app_unexpand_rule PostCond.total
  | `($_ fun $xs* => $e) => do `(⇓ $xs* => $(← SPred.Notation.unpack e))

instance : Inhabited (PostCond α ps) where
  default := ⇓_ => default

@[simp]
abbrev PostCond.entails (p q : PostCond α ps) : Prop :=
  (∀ a, SPred.entails (p.1 a) (q.1 a)) ∧ FailConds.entails p.2 q.2

infixr:25 "⊢ₚ" => PostCond.entails

@[refl,simp]
abbrev PostCond.entails_refl (Q : PostCond α ps) : Q ⊢ₚ Q := by
  simp only [entails, PreCond, SPred.entails.refl, implies_true, FailConds.entails_refl, and_self]

@[simp]
theorem PostCond.total_def {p : α → PreCond ps} : (p, FailConds.false) = PostCond.total p := rfl

@[simp]
theorem PostCond.partial_def {p : α → PreCond ps} : (p, FailConds.true) = PostCond.partial p := rfl

@[simp]
theorem PostCond.entails_total (p : α → PreCond ps) (q : PostCond α ps) : (PostCond.total p) ⊢ₚ q ↔ ∀ a, p a ⊢ₛ q.1 a := by
  simp only [total, entails, FailConds.entails_false, and_true]

@[simp]
theorem PostCond.entails_partial (p : PostCond α ps) (q : α → PreCond ps) : p ⊢ₚ (PostCond.partial q) ↔ ∀ a, p.1 a ⊢ₛ q a := by
  simp only [total, entails, FailConds.entails_true, and_true]
