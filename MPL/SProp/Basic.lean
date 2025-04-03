import Lean

namespace MPL

/-- A value indexed by a list of states. -/
def SVal (σs : List Type) (α : Type) := match σs with
| [] => α
| σ :: σs => σ → SVal σs α
-- Note: SVal is not defined in terms of List.foldr, because that is not reducible.
-- Reducibility is important for simp to apply lemmas such as
--   lemma ite_app {c:Prop} [Decidable c] (t e : α → β) (a : α) : (if c then t else e) a = if c then t a else e a

abbrev SVal.pure {σs : List Type} (a : α) : SVal σs α := match σs with
| [] => a
| σ :: σs => fun (_ : σ) => pure a

abbrev SVal.bind {σs : List Type} {α β : Type} (m : SVal σs α) (f : α → SVal σs β) : SVal σs β := match σs with
| [] => f m
| σ :: σs => fun (s : σ) => bind (m s) (f · s)

instance (σs : List Type) : Monad (SVal σs) where
  pure := SVal.pure
  bind := SVal.bind

instance (σs : List Type) : MonadReaderOf σ (SVal (σ::σs)) where
  read := fun s => pure s

instance (σs : List Type) [MonadReaderOf σ₁ (SVal σs)] : MonadReaderOf σ₁ (SVal (σ₂::σs)) where
  read := fun _ => read

@[simp]
theorem SVal.pure_empty (a : α) : Pure.pure (f:=SVal []) a = a := rfl

/-- A Proposition indexed by a list of states. -/
abbrev SProp (σs : List Type) : Type := SVal σs Prop

def SProp.pure {σs : List Type} (P : Prop) : SProp σs := Pure.pure (f:=SVal σs) P

@[simp]
theorem SProp.pure_empty (P : Prop) : SProp.pure P (σs:=[]) = P := rfl

@[ext]
theorem SProp.ext {σs : List Type} {P Q : SProp (σ::σs)} : (∀ s, P s = Q s) → P = Q := funext

@[simp]
def SProp.entails {σs : List Type} (P Q : SProp σs) : Prop := match σs with
| [] => P → Q
| σ :: _ => ∀ (s : σ), entails (P s) (Q s)

abbrev SProp.and {σs : List Type} (P Q : SProp σs) : SProp σs := match σs with
| [] => P ∧ Q
| σ :: _ => fun (s : σ) => and (P s) (Q s)

abbrev SProp.or {σs : List Type} (P Q : SProp σs) : SProp σs := match σs with
| [] => P ∨ Q
| σ :: _ => fun (s : σ) => or (P s) (Q s)

abbrev SProp.imp {σs : List Type} (P Q : SProp σs) : SProp σs := match σs with
| [] => P → Q
| σ :: _ => fun (s : σ) => imp (P s) (Q s)

abbrev SProp.iff {σs : List Type} (P Q : SProp σs) : SProp σs := and (imp P Q) (imp Q P)

abbrev SProp.exists {α} {σs : List Type} (P : α → SProp σs) : SProp σs := match σs with
| [] => ∃ a, P a
| σ :: _ => fun (s : σ) => «exists» (fun a => P a s)

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
