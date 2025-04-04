import Lean
import MPL.SProp.SVal

namespace MPL

/-- A Proposition indexed by a list of states. -/
abbrev SProp (σs : List Type) : Type := SVal σs Prop

namespace SProp

def idiom {σs : List Type} (P : SVal.EscapeFun σs → Prop) : SProp σs := match σs with
| [] => P SVal.EscapeFun.id
| σ :: _ => fun (s : σ) => idiom (fun f => P (SVal.EscapeFun.cons s f))
@[simp] theorem idiom_nil {P : SVal.EscapeFun [] → Prop} : idiom P = P SVal.EscapeFun.id := rfl
@[simp] theorem idiom_cons {σs : List Type} {P : SVal.EscapeFun (σ::σs) → Prop} {s : σ} : idiom P s = idiom (fun f => P (SVal.EscapeFun.cons s f)) := rfl

/-- A pure proposition `P : Prop` embedded into `SProp`. For internal use in this module only; prefer to use idiom bracket notation `⌜P⌝. -/
@[simp]
private abbrev pure {σs : List Type} (P : Prop) : SProp σs := idiom (fun _ => P)

@[ext]
theorem ext {σs : List Type} {P Q : SProp (σ::σs)} : (∀ s, P s = Q s) → P = Q := funext

def entails {σs : List Type} (P Q : SProp σs) : Prop := match σs with
| [] => P → Q
| σ :: _ => ∀ (s : σ), entails (P s) (Q s)
@[simp] theorem entails_nil {P Q : SProp []} : entails P Q = (P → Q) := rfl

-- Reducibility of entails must be semi-reducible so that entails_refl is useful for rfl

def and {σs : List Type} (P Q : SProp σs) : SProp σs := match σs with
| [] => P ∧ Q
| σ :: _ => fun (s : σ) => and (P s) (Q s)
@[simp] theorem and_nil {P Q : SProp []} : and P Q = (P ∧ Q) := rfl
@[simp] theorem and_cons {σs : List Type} {P Q : SProp (σ::σs)} : and P Q s = and (P s) (Q s) := rfl

def or {σs : List Type} (P Q : SProp σs) : SProp σs := match σs with
| [] => P ∨ Q
| σ :: _ => fun (s : σ) => or (P s) (Q s)
@[simp] theorem or_nil {P Q : SProp []} : or P Q = (P ∨ Q) := rfl
@[simp] theorem or_cons {σs : List Type} {P Q : SProp (σ::σs)} : or P Q s = or (P s) (Q s) := rfl

def imp {σs : List Type} (P Q : SProp σs) : SProp σs := match σs with
| [] => P → Q
| σ :: _ => fun (s : σ) => imp (P s) (Q s)
@[simp] theorem imp_nil {P Q : SProp []} : imp P Q = (P → Q) := rfl
@[simp] theorem imp_cons {σs : List Type} {P Q : SProp (σ::σs)} : imp P Q s = imp (P s) (Q s) := rfl

def iff {σs : List Type} (P Q : SProp σs) : SProp σs := match σs with
| [] => P ↔ Q
| σ :: _ => fun (s : σ) => iff (P s) (Q s)
@[simp] theorem iff_nil {P Q : SProp []} : iff P Q = (P ↔ Q) := rfl
@[simp] theorem iff_cons {σs : List Type} {P Q : SProp (σ::σs)} : iff P Q s = iff (P s) (Q s) := rfl

def «exists» {α} {σs : List Type} (P : α → SProp σs) : SProp σs := match σs with
| [] => ∃ a, P a
| σ :: _ => fun (s : σ) => «exists» (fun a => P a s)
@[simp] theorem exists_nil {α} {P : α → SProp []} : «exists» P = (∃ a, P a) := rfl
@[simp] theorem exists_cons {σs : List Type} {α} {P : α → SProp (σ::σs)} : «exists» P s = «exists» (fun a => P a s) := rfl

def «forall» {α} {σs : List Type} (P : α → SProp σs) : SProp σs := match σs with
| [] => ∀ a, P a
| σ :: _ => fun (s : σ) => «forall» (fun a => P a s)
@[simp] theorem forall_nil {α} {P : α → SProp []} : «forall» P = (∀ a, P a) := rfl
@[simp] theorem forall_cons {σs : List Type} {α} {P : α → SProp (σ::σs)} : «forall» P s = «forall» (fun a => P a s) := rfl

@[refl,simp]
theorem entails_refl {σs : List Type} (P : SProp σs) : P.entails P := by
  match σs with
  | [] => simp[entails]
  | σ :: _ => intro s; exact entails_refl (P s)

theorem entails_trans {σs : List Type} {P Q R : SProp σs} : P.entails Q → Q.entails R → P.entails R := by
  match σs with
  | [] => intro h₁ h₂; exact h₂ ∘ h₁
  | σ :: _ => intro h₁ h₂; intro s; exact entails_trans (h₁ s) (h₂ s)

theorem entails_pure_intro {σs : List Type} (P Q : Prop) : (P → Q) → (pure P).entails (σs := σs) (pure Q) := by
  induction σs <;> simp_all [entails]

@[simp]
theorem entails_pure_elim {σ : Type} {σs : List Type} [Inhabited σ] (P Q : Prop) : (pure P).entails (σs := σ::σs) (pure Q) ↔ (pure P).entails (σs := σs) (pure Q):= by
  induction σs <;> simp [entails, *]

-- consider deriving the simp lemmas below once we need more of them
-- open Lean Elab Meta Term Command in
-- elab "lift_simp_lemma " name:ident : command => do
--   elabCommand (← `(command|
--   @[simp] theorem $name
--   )
--   return

@[simp]
theorem and_true {σs : List Type} (P : SProp σs) : P.and (pure True) = P := by
  induction σs
  case nil => simp only [and, pure, idiom, _root_.and_true]
  case cons σ σs ih => ext s; exact ih (P s)

@[simp]
theorem true_and {σs : List Type} (P : SProp σs) : (pure True).and P = P := by
  induction σs
  case nil => simp only [and, pure, idiom, _root_.true_and]
  case cons σ σs ih => ext s; exact ih (P s)

@[simp]
theorem and_false {σs : List Type} (P : SProp σs) : P.and (pure False) = pure False := by
  induction σs
  case nil => simp only [and, pure, idiom, _root_.and_false]
  case cons σ σs ih => ext s; exact ih (P s)

@[simp]
theorem false_and {σs : List Type} (P : SProp σs) : (pure False).and P = pure False := by
  induction σs
  case nil => simp only [and, pure, idiom, _root_.false_and]
  case cons σ σs ih => ext s; exact ih (P s)

@[simp]
theorem and_self {σs : List Type} (P : SProp σs) : P.and P = P := by
  induction σs
  case nil => simp only [and, pure, idiom, _root_.and_self]
  case cons σ σs ih => ext s; exact ih (P s)
