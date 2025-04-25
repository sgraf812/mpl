/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
import MPL.SPred
import MPL.Utils.UnexpandRule

/-!
# Pre and postconditions

This module defines `PreCond` and `PostCond`, the types which constitute
the pre and postconditions of a Hoare triple of the program logic.

## Predicate shapes

Since `mpl` supports arbitrary monads, `PostCond` must be general enough to
cope with state and exceptions.
For this reason, `PostCond` is indexed by a `PostShape` which is an abstraction
of the stack of effects supported by the monad, corresponding directly to
`StateT` and `ExceptT` layers in a transformer stack.
For every `StateT σ` effect, we get one `PostShape.arg σ` layer, whereas for every
`ExceptT ε` effect, we get one `PostShape.except ε` layer.
Currently, the only supported base layer is `PostShape.pure`.

## Pre and postconditions

The type of preconditions `PreCond ps` is distinct from the type of postconditions `PostCond α ps`.

This is because postconditions not only specify what happens upon successful termination of the
program, but also need to specify a property that holds upon failure.
We get one "barrel" for the success case, plus one barrel per `PostShape.except` layer.

It does not make much sense to talk about failure barrels in the context of preconditions.
Hence, `PreCond ps` is defined such that all `PostShape.except` layers are discarded from `ps`,
via `PostShape.args`.
-/

namespace MPL

inductive PostShape : Type 1 where
  | pure : PostShape
  | arg : (σ : Type) → PostShape → PostShape
  | except : (ε : Type) → PostShape → PostShape

@[simp]
abbrev PostShape.args : PostShape → List Type
  | .pure => []
  | .arg σ s => σ :: PostShape.args s
  | .except _ s => PostShape.args s

/--
  A precondition on the `.arg`s in the given predicate shape.
  ```
  example : PreCond (.arg ρ .pure) = (ρ → Prop) := rfl
  example : PreCond (.except ε .pure) = Prop := rfl
  example : PreCond (.arg σ (.except ε .pure)) = (σ → Prop) := rfl
  example : PreCond (.except ε (.arg σ .pure)) = (σ → Prop) := rfl
  ```
  This is an abbreviation for `SPred` under the hood, so all theorems about `SPred` apply.
-/
abbrev PreCond (ps : PostShape) : Type := SPred (PostShape.args ps)

/--
  Encodes one continuation barrel for each `PostShape.except` in the given predicate shape.
  ```
  example : FailConds (.pure) = Unit := rfl
  example : FailConds (.except ε .pure) = ((ε → Prop) × Unit) := rfl
  example : FailConds (.arg σ (.except ε .pure)) = ((ε → Prop) × Unit) := rfl
  example : FailConds (.except ε (.arg σ .pure)) = ((ε → σ → Prop) × Unit) := rfl
  ```
-/
def FailConds : PostShape → Type
  | .pure => Unit
  | .arg _ ps => FailConds ps
  | .except ε ps => (ε → PreCond ps) × FailConds ps

def FailConds.const {ps : PostShape} (p : Prop) : FailConds ps := match ps with
  | .pure => ()
  | .arg _ ps => @FailConds.const ps p
  | .except _ ps => (fun _ε => spred(⌜p⌝), @FailConds.const ps p)

def FailConds.true : FailConds ps := FailConds.const True
def FailConds.false : FailConds ps := FailConds.const False

instance : Inhabited (FailConds ps) where
  default := FailConds.true

def FailConds.entails {ps : PostShape} (x y : FailConds ps) : Prop :=
  match ps with
  | .pure => True
  | .arg _ ps => @entails ps x y
  | .except _ ps => (∀ e, x.1 e ⊢ₛ y.1 e) ∧ @entails ps x.2 y.2

infixr:25 " ⊢ₑ " => FailConds.entails

@[simp, refl]
theorem FailConds.entails.refl {ps : PostShape} (x : FailConds ps) : x ⊢ₑ x := by
  induction ps <;> simp [entails, *]

theorem FailConds.entails.rfl {ps : PostShape} {x : FailConds ps} : x ⊢ₑ x := refl x

theorem FailConds.entails.trans {ps : PostShape} {x y z : FailConds ps} : (x ⊢ₑ y) → (y ⊢ₑ z) → x ⊢ₑ z := by
  induction ps
  case pure => intro _ _; trivial
  case arg σ s ih => exact ih
  case except ε s ih => intro h₁ h₂; exact ⟨fun e => (h₁.1 e).trans (h₂.1 e), ih h₁.2 h₂.2⟩

@[simp]
theorem FailConds.pure_def {x : FailConds .pure} : x = () := rfl

@[simp]
theorem FailConds.entails_false {x : FailConds ps} : FailConds.false ⊢ₑ x := by
  induction ps <;> simp_all [false, const, entails, SPred.false_elim]

@[simp]
theorem FailConds.entails_true {x : FailConds ps} : x ⊢ₑ FailConds.true := by
  induction ps <;> simp_all [true, const, entails, SPred.true_intro]

/--
  A multi-barreled postcondition for the given predicate shape.
  ```
  example : PostCond α (.arg ρ .pure) = ((α → ρ → Prop) × Unit) := rfl
  example : PostCond α (.except ε .pure) = ((α → Prop) × (ε → Prop) × Unit) := rfl
  example : PostCond α (.arg σ (.except ε .pure)) = ((α → σ → Prop) × (ε → Prop) × Unit) := rfl
  example : PostCond α (.except ε (.arg σ .pure)) = ((α → σ → Prop) × (ε → σ → Prop) × Unit) := rfl
  ```
-/
abbrev PostCond (α : Type) (s : PostShape) : Type :=
  (α → PreCond s) × FailConds s

/-- A postcondition expressing total correctness. -/
abbrev PostCond.total (p : α → PreCond ps) : PostCond α ps :=
  (p, FailConds.false)

/-- A postcondition expressing partial correctness. -/
abbrev PostCond.partial (p : α → PreCond ps) : PostCond α ps :=
  (p, FailConds.true)

example : Unit × Unit := ⟨(), ()⟩
open Lean Parser Term in
def post_syntax := leading_parser
  "post⟨" >> withoutPosition (withoutForbidden (sepBy termParser ", " (allowTrailingSep := true))) >> "⟩"
syntax:max post_syntax : term
macro_rules | `(post⟨$handlers,*⟩) => `(by exact ⟨$handlers,*, ()⟩)
  -- NB: Postponement through by exact is the entire point of this macro
  -- until https://github.com/leanprover/lean4/pull/8074 lands
example : PostCond Nat .pure := post⟨fun s => True⟩
example : PostCond (Nat × Nat) (PostShape.except Nat (PostShape.arg Nat PostShape.pure)) :=
  post⟨fun (r, xs) s => r ≤ 4 ∧ s = 4 ∧ r + xs > 4, fun e s => e = 42 ∧ s = 4⟩

open Lean Parser Term in
def funArrow : Parser := unicodeSymbol " ↦ " " => "
@[inherit_doc PostCond.total]
macro "⇓" xs:Lean.Parser.Term.funBinder+ funArrow e:term : term =>
  `(PostCond.total (by exact (fun $xs* => spred($e)))) -- NB: Postponement through by exact
app_unexpand_rule PostCond.total
  | `($_ fun $xs* => $e) => do `(⇓ $xs* => $(← SPred.Notation.unpack e))

instance : Inhabited (PostCond α ps) where
  default := ⇓_ => default

@[simp]
def PostCond.entails (p q : PostCond α ps) : Prop :=
  (∀ a, SPred.entails (p.1 a) (q.1 a)) ∧ FailConds.entails p.2 q.2

infixr:25 " ⊢ₚ " => PostCond.entails

@[refl,simp]
theorem PostCond.entails.refl (Q : PostCond α ps) : Q ⊢ₚ Q := ⟨fun a => SPred.entails.refl (Q.1 a), FailConds.entails.refl Q.2⟩
theorem PostCond.entails.rfl {Q : PostCond α ps} : Q ⊢ₚ Q := refl Q

theorem PostCond.entails.trans {P Q R : PostCond α ps} (h₁ : P ⊢ₚ Q) (h₂ : Q ⊢ₚ R) : P ⊢ₚ R :=
  ⟨fun a => (h₁.1 a).trans (h₂.1 a), h₁.2.trans h₂.2⟩

@[simp]
theorem PostCond.entails_total (p : α → PreCond ps) (q : PostCond α ps) : PostCond.total p ⊢ₚ q ↔ ∀ a, p a ⊢ₛ q.1 a := by
  simp only [total, entails, FailConds.entails_false, and_true]

@[simp]
theorem PostCond.entails_partial (p : PostCond α ps) (q : α → PreCond ps) : p ⊢ₚ PostCond.partial q ↔ ∀ a, p.1 a ⊢ₛ q a := by
  simp only [total, entails, FailConds.entails_true, and_true]
