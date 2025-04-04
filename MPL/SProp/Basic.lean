import Lean

namespace MPL

/-- A value indexed by a list of states. -/
abbrev SVal (σs : List Type) (α : Type) := match σs with
| [] => α
| σ :: σs => σ → SVal σs α

abbrev SVal.pure {σs : List Type} (a : α) : SVal σs α := match σs with
| [] => a
| σ :: σs => fun (_ : σ) => pure a

/- Note about the reducibility of SVal:
We need SVal to be reducible, so that simp can apply lemmas such as
  lemma ite_app {c:Prop} [Decidable c] (t e : α → β) (a : α) : (if c then t else e) a = if c then t a else e a
-/

@[simp]
theorem SVal.pure_empty (a : α) : SVal.pure (σs:=[]) a = a := rfl

/-- A Proposition indexed by a list of states. -/
abbrev SProp (σs : List Type) : Type := SVal σs Prop

@[simp]
def SProp.idiom {σs : List Type} (P : (∀ α, SVal σs α → α) → Prop) : SProp σs := match σs with
| [] => P (fun α m => m)
| σ :: σs => fun (s : σ) => SProp.idiom (fun f => P (fun α m => f α (m s)))

class SVal.GetTy (σ : Type) (σs : List Type) where
  get : SVal σs σ

instance : SVal.GetTy σ (σ :: σs) where
  get := fun s => SVal.pure s

instance [SVal.GetTy σ₁ σs] : SVal.GetTy σ₁ (σ₂ :: σs) where
  get := fun _ => SVal.GetTy.get

abbrev SVal.GetTy.applyEscape {σs : List Type} (f : SVal σs σ) (escape : ∀ α, SVal σs α → α) : σ := escape σ f
abbrev SVal.getThe {σs : List Type} (σ : Type) [SVal.GetTy σ σs] : SVal σs σ := SVal.GetTy.get

@[simp]
theorem SProp.idiom_empty {P : (∀ α, SVal [] α → α) → Prop} : SProp.idiom (σs:=[]) P = P @id := rfl

@[simp]
theorem SProp.idiom_apply {σs : List Type} {P : (∀ α, SVal (σ::σs) α → α) → Prop} {s : σ} : SProp.idiom (σs:=σ::σs) P s = SProp.idiom (fun escape => P (fun α m => escape α (m s))) := rfl

/-- A pure proposition `P : Prop` embedded into `SProp`. For internal use in this module only; prefer to use idiom bracket notation `⌜P⌝. -/
@[simp]
private abbrev SProp.pure {σs : List Type} (P : Prop) : SProp σs := SProp.idiom (fun _ => P)

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

@[simp]
abbrev SProp.iff {σs : List Type} (P Q : SProp σs) : SProp σs := match σs with
| [] => P ↔ Q
| σ :: _ => fun (s : σ) => iff (P s) (Q s)

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
  case nil => simp only [and, pure, idiom, _root_.and_true]
  case cons σ σs ih => ext s; exact ih (P s)

@[simp]
theorem SProp.true_and {σs : List Type} (P : SProp σs) : (pure True).and P = P := by
  induction σs
  case nil => simp only [and, pure, idiom, _root_.true_and]
  case cons σ σs ih => ext s; exact ih (P s)

@[simp]
theorem SProp.and_false {σs : List Type} (P : SProp σs) : P.and (pure False) = pure False := by
  induction σs
  case nil => simp only [and, pure, idiom, _root_.and_false]
  case cons σ σs ih => ext s; exact ih (P s)

@[simp]
theorem SProp.false_and {σs : List Type} (P : SProp σs) : (pure False).and P = pure False := by
  induction σs
  case nil => simp only [and, pure, idiom, _root_.false_and]
  case cons σ σs ih => ext s; exact ih (P s)

@[simp]
theorem SProp.and_self {σs : List Type} (P : SProp σs) : P.and P = P := by
  induction σs
  case nil => simp only [and, pure, idiom, _root_.and_self]
  case cons σ σs ih => ext s; exact ih (P s)
