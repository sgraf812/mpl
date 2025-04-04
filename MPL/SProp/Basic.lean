import Lean
import Init.Data.List

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

def SProp.EscapeFun (σs : List Type) := { f : ∀ α, SVal σs α → α // ∀ α (a : α), f α (SVal.pure a) = a }
def SProp.EscapeFun.id : SProp.EscapeFun [] := ⟨fun α m => m, fun α a => rfl⟩
def SProp.EscapeFun.cons (s : σ) (fn : SProp.EscapeFun σs) : SProp.EscapeFun (σ::σs) :=
  ⟨fun α m => fn.1 α (m s), fn.2⟩

def SProp.idiom {σs : List Type} (P : SProp.EscapeFun σs → Prop) : SProp σs := match σs with
| [] => P SProp.EscapeFun.id
| σ :: σs => fun (s : σ) => SProp.idiom (fun f => P (SProp.EscapeFun.cons s f))
@[simp] theorem SProp.idiom_nil {P : SProp.EscapeFun [] → Prop} : SProp.idiom P = P SProp.EscapeFun.id := rfl
@[simp] theorem SProp.idiom_cons {σs : List Type} {P : SProp.EscapeFun (σ::σs) → Prop} {s : σ} : SProp.idiom P s = SProp.idiom (fun f => P (SProp.EscapeFun.cons s f)) := rfl

class SVal.GetTy (σ : Type) (σs : List Type) where
  get : SVal σs σ

@[simp]
instance : SVal.GetTy σ (σ :: σs) where
  get := fun s => SVal.pure s

@[simp]
instance [SVal.GetTy σ₁ σs] : SVal.GetTy σ₁ (σ₂ :: σs) where
  get := fun _ => SVal.GetTy.get

def SVal.GetTy.applyEscape {σs : List Type} (f : SVal σs σ) (escape : SProp.EscapeFun σs) : σ := escape.1 σ f
def SVal.getThe {σs : List Type} (σ : Type) [SVal.GetTy σ σs] : SVal σs σ := SVal.GetTy.get

/-- A pure proposition `P : Prop` embedded into `SProp`. For internal use in this module only; prefer to use idiom bracket notation `⌜P⌝. -/
@[simp]
private abbrev SProp.pure {σs : List Type} (P : Prop) : SProp σs := SProp.idiom (fun _ => P)

@[ext]
theorem SProp.ext {σs : List Type} {P Q : SProp (σ::σs)} : (∀ s, P s = Q s) → P = Q := funext

def SProp.entails {σs : List Type} (P Q : SProp σs) : Prop := match σs with
| [] => P → Q
| σ :: _ => ∀ (s : σ), entails (P s) (Q s)
@[simp] theorem SProp.entails_nil {P Q : SProp []} : SProp.entails P Q = (P → Q) := rfl

-- Reducibility of SProp.entails must be semi-reducible so that SProp.entails_refl is useful for rfl

def SProp.and {σs : List Type} (P Q : SProp σs) : SProp σs := match σs with
| [] => P ∧ Q
| σ :: _ => fun (s : σ) => and (P s) (Q s)
@[simp] theorem SProp.and_nil {P Q : SProp []} : SProp.and P Q = (P ∧ Q) := rfl
@[simp] theorem SProp.and_cons {σs : List Type} {P Q : SProp (σ::σs)} : SProp.and P Q s = SProp.and (P s) (Q s) := rfl

def SProp.or {σs : List Type} (P Q : SProp σs) : SProp σs := match σs with
| [] => P ∨ Q
| σ :: _ => fun (s : σ) => or (P s) (Q s)
@[simp] theorem SProp.or_nil {P Q : SProp []} : SProp.or P Q = (P ∨ Q) := rfl
@[simp] theorem SProp.or_cons {σs : List Type} {P Q : SProp (σ::σs)} : SProp.or P Q s = SProp.or (P s) (Q s) := rfl

def SProp.imp {σs : List Type} (P Q : SProp σs) : SProp σs := match σs with
| [] => P → Q
| σ :: _ => fun (s : σ) => imp (P s) (Q s)
@[simp] theorem SProp.imp_nil {P Q : SProp []} : SProp.imp P Q = (P → Q) := rfl
@[simp] theorem SProp.imp_cons {σs : List Type} {P Q : SProp (σ::σs)} : SProp.imp P Q s = SProp.imp (P s) (Q s) := rfl

def SProp.iff {σs : List Type} (P Q : SProp σs) : SProp σs := match σs with
| [] => P ↔ Q
| σ :: _ => fun (s : σ) => iff (P s) (Q s)
@[simp] theorem SProp.iff_nil {P Q : SProp []} : SProp.iff P Q = (P ↔ Q) := rfl
@[simp] theorem SProp.iff_cons {σs : List Type} {P Q : SProp (σ::σs)} : SProp.iff P Q s = SProp.iff (P s) (Q s) := rfl

def SProp.exists {α} {σs : List Type} (P : α → SProp σs) : SProp σs := match σs with
| [] => ∃ a, P a
| σ :: _ => fun (s : σ) => «exists» (fun a => P a s)
@[simp] theorem SProp.exists_nil {α} {P : α → SProp []} : SProp.exists P = (∃ a, P a) := rfl
@[simp] theorem SProp.exists_cons {σs : List Type} {α} {P : α → SProp (σ::σs)} : SProp.exists P s = SProp.exists (fun a => P a s) := rfl

def SProp.forall {α} {σs : List Type} (P : α → SProp σs) : SProp σs := match σs with
| [] => ∀ a, P a
| σ :: _ => fun (s : σ) => «forall» (fun a => P a s)
@[simp] theorem SProp.forall_nil {α} {P : α → SProp []} : SProp.forall P = (∀ a, P a) := rfl
@[simp] theorem SProp.forall_cons {σs : List Type} {α} {P : α → SProp (σ::σs)} : SProp.forall P s = SProp.forall (fun a => P a s) := rfl

@[refl,simp]
theorem SProp.entails_refl {σs : List Type} (P : SProp σs) : P.entails P := by
  match σs with
  | [] => simp[SProp.entails]
  | σ :: _ => intro s; exact entails_refl (P s)

theorem SProp.entails_trans {σs : List Type} {P Q R : SProp σs} : P.entails Q → Q.entails R → P.entails R := by
  match σs with
  | [] => intro h₁ h₂; exact h₂ ∘ h₁
  | σ :: _ => intro h₁ h₂; intro s; exact entails_trans (h₁ s) (h₂ s)

theorem SProp.entails_pure_intro {σs : List Type} (P Q : Prop) : (P → Q) → (pure P).entails (σs := σs) (pure Q) := by
  induction σs <;> simp_all [SProp.entails]

@[simp]
theorem SProp.entails_pure_elim {σ : Type} {σs : List Type} [Inhabited σ] (P Q : Prop) : (pure P).entails (σs := σ::σs) (pure Q) ↔ (pure P).entails (σs := σs) (pure Q):= by
  induction σs <;> simp [SProp.entails, *]

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

@[simp] theorem SVal.getThe_here {σs : List Type} (σ : Type) (s : σ) : SVal.getThe (σs := σ::σs) σ s = SVal.pure s := rfl
@[simp] theorem SVal.getThe_there {σs : List Type} [SVal.GetTy σ σs] (σ' : Type) (s : σ') : SVal.getThe (σs := σ'::σs) σ s = SVal.getThe (σs := σs) σ := rfl

@[simp]
theorem SVal.GetTy.applyEscape_pure {σs : List Type} {s : σ} {escape : SProp.EscapeFun σs} :
  SVal.GetTy.applyEscape (σs:=σs) (SVal.pure s) escape = s := by simp[applyEscape, escape.property]

@[simp]
theorem SVal.GetTy.applyEscape_id {m : SVal [] α} :
  SVal.GetTy.applyEscape m SProp.EscapeFun.id = m := rfl

@[simp]
theorem SVal.GetTy.applyEscape_cons {σs : List Type} {s : σ} {m : SVal (σ::σs) α} {escape : SProp.EscapeFun σs} :
  SVal.GetTy.applyEscape (σs:=(σ::σs)) m (SProp.EscapeFun.cons s escape) = SVal.GetTy.applyEscape (m s) escape := rfl
