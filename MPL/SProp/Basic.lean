import Lean

namespace MPL

/-- A value indexed by a list of states. -/
abbrev SVal (σs : List Type) (α : Type) := match σs with
| [] => α
| σ :: σs => σ → SVal σs α

/- Note about the reducibility of SVal:
We need SVal to be reducible, so that simp can apply lemmas such as
  lemma ite_app {c:Prop} [Decidable c] (t e : α → β) (a : α) : (if c then t else e) a = if c then t a else e a
However, this makes it impossible to define a `Monad` instance for `SVal σs`.
We need such a monad instance for idiom bracket notation of `SProp`.
Hence we define a wrapper type `SVal.M` that is semi-reducible and has the proper `Monad` instance.
-/

/-- A semi-reducible wrapper around `SVal` equipped with a `Monad` instance. -/
def SVal.M : List Type → Type → Type := SVal

abbrev SVal.M.pure {σs : List Type} (a : α) : SVal σs α := match σs with
| [] => a
| σ :: σs => fun (_ : σ) => pure a

abbrev SVal.M.bind {σs : List Type} {α β : Type} (m : SVal σs α) (f : α → SVal σs β) : SVal σs β := match σs with
| [] => f m
| σ :: σs => fun (s : σ) => bind (m s) (f · s)

instance (σs : List Type) : Monad (SVal.M σs) where
  pure := SVal.M.pure
  bind := SVal.M.bind

instance (σs : List Type) : MonadReaderOf σ (SVal.M (σ::σs)) where
  read := fun s => pure (f:=SVal.M σs) s

instance (σs : List Type) [MonadReaderOf σ₁ (SVal.M σs)] : MonadReaderOf σ₁ (SVal.M (σ₂::σs)) where
  read := fun _ => read (m:=SVal.M σs)

@[simp]
theorem SVal.M.pure_empty (a : α) : Pure.pure (f:=SVal.M []) a = a := rfl

/-- A Proposition indexed by a list of states. -/
abbrev SProp (σs : List Type) : Type := SVal σs Prop

abbrev SProp.pure {σs : List Type} (P : Prop) : SProp σs := SVal.M.pure P

@[simp]
theorem SProp.pure_empty (P : Prop) : SProp.pure P (σs:=[]) = P := rfl

@[simp]
theorem SProp.pure_apply (P : Prop) (s : σ) : SProp.pure (σs:=σ::σs) P s = SProp.pure P := rfl

@[ext]
theorem SProp.ext {σs : List Type} {P Q : SProp (σ::σs)} : (∀ s, P s = Q s) → P = Q := funext

@[simp]
def SProp.entails {σs : List Type} (P Q : SProp σs) : Prop := match σs with
| [] => P → Q
| σ :: _ => ∀ (s : σ), entails (P s) (Q s)

@[simp]
abbrev SProp.and {σs : List Type} (P Q : SProp σs) : SProp σs := match σs with
| [] => P ∧ Q
| σ :: _ => fun (s : σ) => and (P s) (Q s)

@[simp]
abbrev SProp.or {σs : List Type} (P Q : SProp σs) : SProp σs := match σs with
| [] => P ∨ Q
| σ :: _ => fun (s : σ) => or (P s) (Q s)

@[simp]
abbrev SProp.imp {σs : List Type} (P Q : SProp σs) : SProp σs := match σs with
| [] => P → Q
| σ :: _ => fun (s : σ) => imp (P s) (Q s)

abbrev SProp.iff {σs : List Type} (P Q : SProp σs) : SProp σs := and (imp P Q) (imp Q P)
@[simp]
theorem SProp.iff_apply {σs : List Type} {P Q : SProp (σ::σs)} (s : σ) : (P.iff Q) s = SProp.iff (P s) (Q s) := by simp[SProp.iff]

@[simp]
abbrev SProp.exists {α} {σs : List Type} (P : α → SProp σs) : SProp σs := match σs with
| [] => ∃ a, P a
| σ :: _ => fun (s : σ) => «exists» (fun a => P a s)

@[simp]
abbrev SProp.forall {α} {σs : List Type} (P : α → SProp σs) : SProp σs := match σs with
| [] => ∀ a, P a
| σ :: _ => fun (s : σ) => «forall» (fun a => P a s)

@[refl,simp]
theorem SProp.entails_refl {σs : List Type} (P : SProp σs) : P.entails P := by
  match σs with
  | [] => simp[SProp.entails]
  | σ :: _ => intro s; exact entails_refl (P s)

theorem SProp.entails_trans {σs : List Type} {P Q R : SProp σs} : P.entails Q → Q.entails R → P.entails R := by
  match σs with
  | [] => intro h₁ h₂; exact h₂ ∘ h₁
  | σ :: _ => intro h₁ h₂; intro s; exact entails_trans (h₁ s) (h₂ s)

-- consider deriving the simp lemmas below once we need more of them
-- open Lean Elab Meta Term Command in
-- elab "lift_simp_lemma " name:ident : command => do
--   elabCommand (← `(command|
--   @[simp] theorem SProp.$name
--   )
--   return

@[simp]
theorem SProp.and_true {σs : List Type} (P : SProp σs) : P.and (pure True) = P := by
  induction σs
  case nil => simp only [_root_.and_true, SProp.pure_empty]
  case cons σ σs ih => ext s; exact ih (P s)

@[simp]
theorem SProp.true_and {σs : List Type} (P : SProp σs) : (pure True).and P = P := by
  induction σs
  case nil => simp only [_root_.true_and, SProp.pure_empty]
  case cons σ σs ih => ext s; exact ih (P s)

@[simp]
theorem SProp.and_false {σs : List Type} (P : SProp σs) : P.and (pure False) = pure False := by
  induction σs
  case nil => simp only [_root_.and_false, SProp.pure_empty]
  case cons σ σs ih => ext s; exact ih (P s)

@[simp]
theorem SProp.false_and {σs : List Type} (P : SProp σs) : (pure False).and P = pure False := by
  induction σs
  case nil => simp only [_root_.false_and, SProp.pure_empty]
  case cons σ σs ih => ext s; exact ih (P s)

@[simp]
theorem SProp.and_self {σs : List Type} (P : SProp σs) : P.and P = P := by
  induction σs
  case nil => simp only [_root_.and_self, SProp.pure_empty]
  case cons σ σs ih => ext s; exact ih (P s)

@[simp]
def SProp.idiom {σs : List Type} (P : SVal.M σs Prop) : SProp σs := P
