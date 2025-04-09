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
private abbrev pure {σs : List Type} (P : Prop) : SProp σs := idiom (fun _ => P)

@[ext]
theorem ext {σs : List Type} {P Q : SProp (σ::σs)} : (∀ s, P s = Q s) → P = Q := funext

def entails {σs : List Type} (P Q : SProp σs) : Prop := match σs with
| [] => P → Q
| σ :: _ => ∀ (s : σ), entails (P s) (Q s)
@[simp] theorem entails_nil {P Q : SProp []} : entails P Q = (P → Q) := rfl

-- Reducibility of entails must be semi-reducible so that entails_refl is useful for rfl

def bientails {σs : List Type} (P Q : SProp σs) : Prop := match σs with
| [] => P ↔ Q
| σ :: _ => ∀ (s : σ), bientails (P s) (Q s)
@[simp] theorem bientails_nil {P Q : SProp []} : bientails P Q = (P ↔ Q) := rfl
theorem bientails_cons_intro {σs : List Type} {P Q : SProp (σ::σs)} : (∀ s, bientails (P s) (Q s)) → bientails P Q := by simp only [bientails, imp_self]

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

def not {σs : List Type} (P : SProp σs) : SProp σs := match σs with
| [] => ¬ P
| σ :: _ => fun (s : σ) => not (P s)
@[simp] theorem not_nil {P : SProp []} : not P = (¬ P) := rfl
@[simp] theorem not_cons {σs : List Type} {P : SProp (σ::σs)} : not P s = not (P s) := rfl

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

def conjunction {σs : List Type} (env : List (SProp σs)) : SProp σs := match env with
| [] => pure True
| P::env => P.and (conjunction env)
@[simp] theorem conjunction_nil {σs : List Type} : conjunction ([] : List (SProp σs)) = pure True := rfl
@[simp] theorem conjunction_cons {σs : List Type} {P : SProp σs} {env : List (SProp σs)} : conjunction (P::env) = P.and (conjunction env) := rfl
@[simp] theorem conjunction_apply {σs : List Type} {env : List (SProp (σ::σs))} : conjunction env s = conjunction (env.map (· s)) := by
  induction env <;> simp[conjunction, *]
