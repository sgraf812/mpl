import MPL.SProp.Notation

namespace MPL.SProp

@[refl,simp]
theorem entails_refl {σs : List Type} (P : SProp σs) : P ⊢ₛ P := by
  match σs with
  | [] => simp[entails]
  | σ :: _ => intro s; exact entails_refl (P s)

theorem entails_trans {σs : List Type} {P Q R : SProp σs} : (P ⊢ₛ Q) → (Q ⊢ₛ R) → (P ⊢ₛ R) := by
  match σs with
  | [] => intro h₁ h₂; exact h₂ ∘ h₁
  | σ :: _ => intro h₁ h₂; intro s; exact entails_trans (h₁ s) (h₂ s)

theorem entails_pure_intro {σs : List Type} (P Q : Prop) : (P → Q) → ⌜P⌝.entails (σs := σs) ⌜Q⌝ := by
  induction σs <;> simp_all [entails]

@[simp]
theorem entails_pure_elim {σ : Type} {σs : List Type} [Inhabited σ] (P Q : Prop) : ⌜P⌝.entails (σs := σ::σs) ⌜Q⌝ ↔ ⌜P⌝.entails (σs := σs) ⌜Q⌝:= by
  induction σs <;> simp [entails, *]

-- consider deriving the simp lemmas below once we need more of them
-- open Lean Elab Meta Term Command in
-- elab "lift_simp_lemma " name:ident : command => do
--   elabCommand (← `(command|
--   @[simp] theorem $name
--   )
--   return

@[simp]
theorem and_true {σs : List Type} (P : SProp σs) : sprop(P ∧ ⌜True⌝) = P := by
  induction σs
  case nil => simp only [and, pure, idiom, _root_.and_true]
  case cons σ σs ih => ext s; exact ih (P s)

@[simp]
theorem true_and {σs : List Type} (P : SProp σs) : sprop(⌜True⌝ ∧ P) = P := by
  induction σs
  case nil => simp only [and, pure, idiom, _root_.true_and]
  case cons σ σs ih => ext s; exact ih (P s)

@[simp]
theorem and_false {σs : List Type} (P : SProp σs) : sprop(P ∧ ⌜False⌝) = ⌜False⌝ := by
  induction σs
  case nil => simp only [and, pure, idiom, _root_.and_false]
  case cons σ σs ih => ext s; exact ih (P s)

@[simp]
theorem false_and {σs : List Type} (P : SProp σs) : sprop(⌜False⌝ ∧ P) = ⌜False⌝ := by
  induction σs
  case nil => simp only [and, pure, idiom, _root_.false_and]
  case cons σ σs ih => ext s; exact ih (P s)

@[simp]
theorem and_self {σs : List Type} (P : SProp σs) : sprop(P ∧ P) = P := by
  induction σs
  case nil => simp only [and, pure, idiom, _root_.and_self]
  case cons σ σs ih => ext s; exact ih (P s)

@[simp]
theorem and_imp {σs : List Type} (a b c : SProp σs) : sprop(a ∧ b → c) = sprop(a → b → c) := by
  induction σs
  case nil => simp only [imp, and, _root_.and_imp]
  case cons σ σs ih => ext s; exact ih (a s) (b s) (c s)

@[simp]
theorem imp_self {σs : List Type} (P : SProp σs) : sprop(P → P) = ⌜True⌝ := by
  induction σs
  case nil => simp only [imp, pure, idiom, _root_.imp_self]
  case cons σ σs ih => ext s; exact ih (P s)

@[simp]
theorem entails_true_intro {σs : List Type} (P Q : SProp σs) : ⌜True⌝ ⊢ₛ P → Q ↔ P ⊢ₛ Q := by
  induction σs
  case nil => simp only [pure, idiom_nil, imp_nil, entails_nil, forall_const]
  case cons σ σs ih => simp only [entails, idiom_cons, imp, ih]
