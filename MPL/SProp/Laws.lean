import MPL.SProp.Notation

namespace MPL.SProp

/- This module contains lemmas that need to be proved by induction on σs.
That is, they need to proved by appealing to the model of `SProp` and cannot
be derived without doing so. -/

/-! # Entailment -/

@[refl,simp]
theorem entails.refl {σs : List Type} (P : SProp σs) : P ⊢ₛ P := by
  match σs with
  | [] => simp[entails]
  | σ :: _ => intro s; exact entails.refl (P s)

theorem entails.trans {σs : List Type} {P Q R : SProp σs} : (P ⊢ₛ Q) → (Q ⊢ₛ R) → (P ⊢ₛ R) := by
  match σs with
  | [] => intro h₁ h₂; exact h₂ ∘ h₁
  | σ :: _ => intro h₁ h₂; intro s; exact entails.trans (h₁ s) (h₂ s)

instance {σs : List Type} : Trans (@entails σs) entails entails where
  trans := entails.trans

/-! # Bientailment -/

theorem bientails.iff {σs : List Type} {P Q : SProp σs} : P ⊣⊢ₛ Q ↔ (P ⊢ₛ Q) ∧ (Q ⊢ₛ P) := by
  induction σs with
  | nil => exact Iff.intro (fun h => ⟨h.mp, h.mpr⟩) (fun h => ⟨h.1, h.2⟩)
  | cons σ σs ih =>
  apply Iff.intro
  · exact fun h => ⟨fun s => (ih.mp (h s)).1, fun s => (ih.mp (h s)).2⟩
  · intro h s; exact ih.mpr ⟨h.1 s, h.2 s⟩

@[refl,simp]
theorem bientails.refl {σs : List Type} (P : SProp σs) : P ⊣⊢ₛ P := by
  induction σs <;> simp[bientails, *]

theorem bientails.trans {σs : List Type} {P Q R : SProp σs} : (P ⊣⊢ₛ Q) → (Q ⊣⊢ₛ R) → (P ⊣⊢ₛ R) := by
  induction σs
  case nil => simp +contextual only [bientails, implies_true]
  case cons σ σs ih => intro hpq hqr s; exact ih (hpq s) (hqr s)

instance {σs : List Type} : Trans (@bientails σs) bientails bientails where
  trans := bientails.trans

theorem bientails.symm {σs : List Type} {P Q : SProp σs} : (P ⊣⊢ₛ Q) → (Q ⊣⊢ₛ P) := by
  induction σs
  case nil => exact Iff.symm
  case cons σ σs ih => intro h s; exact ih (h s)

/-! # Pure -/

theorem pure_intro {σs : List Type} {φ : Prop} {P : SProp σs} : φ → P ⊢ₛ ⌜φ⌝ := by
  induction σs <;> simp_all [entails]

theorem pure_elim' {σs : List Type} {φ : Prop} {P : SProp σs} : (φ → ⌜True⌝ ⊢ₛ P) → ⌜φ⌝ ⊢ₛ P := by
  induction σs <;> simp_all [entails]

/-! # Conjunction -/

theorem and_intro {σs : List Type} {P Q R : SProp σs} (h1 : P ⊢ₛ Q) (h2 : P ⊢ₛ R) : P ⊢ₛ Q ∧ R := by
  induction σs <;> simp_all [entails]

theorem and_elim_l {P Q : SProp σs} : P ∧ Q ⊢ₛ P := by
  induction σs <;> simp_all [entails]

theorem and_elim_r {P Q : SProp σs} : P ∧ Q ⊢ₛ Q := by
  induction σs <;> simp_all [entails]

/-! # Disjunction -/

theorem or_intro_l {σs : List Type} {P Q : SProp σs} : P ⊢ₛ P ∨ Q := by
  induction σs <;> simp_all [entails]

theorem or_intro_r {σs : List Type} {P Q : SProp σs} : Q ⊢ₛ P ∨ Q := by
  induction σs <;> simp_all [entails]

theorem or_elim {σs : List Type} {P Q R : SProp σs} (h1 : P ⊢ₛ R) (h2 : Q ⊢ₛ R) : P ∨ Q ⊢ₛ R := by
  induction σs
  case nil => exact (Or.elim · h1 h2)
  case cons => simp_all [entails]

/-! # Implication -/

theorem imp_intro {σs : List Type} {P Q R : SProp σs} (h : P ∧ Q ⊢ₛ R) : P ⊢ₛ Q → R := by
  induction σs <;> simp_all [entails]

theorem imp_elim {σs : List Type} {P Q R : SProp σs} (h : P ⊢ₛ Q → R) : P ∧ Q ⊢ₛ R := by
  induction σs <;> simp_all [entails]

/-! # Quantifiers -/

theorem forall_intro {σs : List Type} {P : SProp σs} {Ψ : α → SProp σs} (h : ∀ a, P ⊢ₛ Ψ a) : P ⊢ₛ ∀ a, Ψ a := by
  induction σs <;> simp_all [entails]

theorem forall_elim {σs : List Type} {Ψ : α → SProp σs} (a : α) : (∀ a, Ψ a) ⊢ₛ Ψ a := by
  induction σs <;> simp_all [entails]

theorem exists_intro {σs : List Type} {Ψ : α → SProp σs} (a : α) : Ψ a ⊢ₛ ∃ a, Ψ a := by
  induction σs
  case nil => intro _; exists a
  case cons σ σs ih => intro s; exact @ih (fun a => Ψ a s)

theorem exists_elim {σs : List Type} {Φ : α → SProp σs} {Q : SProp σs} (h : ∀ a, Φ a ⊢ₛ Q) : (∃ a, Φ a) ⊢ₛ Q := by
  induction σs
  case nil => intro ⟨a, ha⟩; exact h a ha
  case cons σ σs ih => intro s; exact ih (fun a => h a s)
