import MPL.ProofMode

open MPL

variable (σs : List Type)

theorem start_stop (Q : SPred σs) (H : Q ⊢ₛ Q) : Q ⊢ₛ Q := by
  sstart
  sintro HQ
  sstop
  exact H

theorem exact (Q : SPred σs) : Q ⊢ₛ Q := by
  sstart
  sintro HQ
  sexact HQ

theorem clear (P Q : SPred σs) : P ⊢ₛ Q → Q := by
  sintro HP
  sintro HQ
  sclear HP
  sexact HQ

theorem assumption (P Q : SPred σs) : Q ⊢ₛ P → Q := by
  sintro _ _
  sassumption

theorem assumption_pure (P Q : SPred σs) (hP : ⊢ₛ P): Q ⊢ₛ P := by
  sintro _
  sassumption

namespace pure

theorem move (Q : SPred σs) : ⌜φ⌝ ⊢ₛ Q → Q := by
  sintro Hφ
  sintro HQ
  spure Hφ
  sexact HQ

theorem move_multiple (Q : SPred σs) : ⌜φ₁⌝ ⊢ₛ ⌜φ₂⌝ → Q → Q := by
  sintro Hφ1
  sintro Hφ2
  sintro HQ
  spure Hφ1
  spure Hφ2
  sexact HQ

theorem move_conjunction (Q : SPred σs) : (⌜φ₁⌝ ∧ ⌜φ₂⌝) ⊢ₛ Q → Q := by
  sintro Hφ
  sintro HQ
  spure Hφ
  sexact HQ

end pure

namespace pureintro

theorem simple : ⊢ₛ (⌜True⌝ : SPred σs) := by
  spure_intro
  exact True.intro

theorem or : ⊢ₛ ⌜True⌝ ∨ (⌜False⌝ : SPred σs) := by
  spure_intro
  left
  exact True.intro

theorem with_proof (H : A → B) (P Q : SPred σs) : P ⊢ₛ Q → ⌜A⌝ → ⌜B⌝ := by
  sintro _HP _HQ
  spure_intro
  exact H

end pureintro

namespace constructor

theorem and (Q : SPred σs) : Q ⊢ₛ Q ∧ Q := by
  sintro HQ
  sconstructor
  <;> sexact HQ

end constructor

namespace leftright

theorem left (P Q : SPred σs) : P ⊢ₛ P ∨ Q := by
  sintro HP
  sleft
  sexact HP

theorem right (P Q : SPred σs) : Q ⊢ₛ P ∨ Q := by
  sintro HQ
  sright
  sexact HQ

theorem complex (P Q R : SPred σs) : ⊢ₛ P → Q → P ∧ (R ∨ Q ∨ R) := by
  sintro HP HQ
  sconstructor
  · sassumption
  sright
  sleft
  sexact HQ

end leftright

namespace specialize

theorem simple (P Q : SPred σs) : P ⊢ₛ (P → Q) → Q := by
  sintro HP HPQ
  sspecialize HPQ HP
  sexact HPQ

theorem multiple (P Q R : SPred σs) : ⊢ₛ P → Q → (P → Q → R) → R := by
  sintro HP HQ HPQR
  sspecialize HPQR HP HQ
  sexact HPQR

theorem pure_imp (P Q R : SPred σs) : (⊢ₛ P) → ⊢ₛ Q → (P → Q → R) → R := by
  intro HP
  sintro HQ HPQR
  sspecialize HPQR HP HQ
  sexact HPQR

theorem forall' (y : Nat) (Q : Nat → SPred σs) : ⊢ₛ (∀ x, Q x) → Q (y + 1) := by
  sintro HQ
  sspecialize HQ (y + 1)
  sexact HQ

theorem mixed (y : Nat) (P Q : SPred σs) (Ψ : Nat → SPred σs) (hP : ⊢ₛ P) : ⊢ₛ Q → (∀ x, P → Q → Ψ x) → Ψ (y + 1) := by
  sintro HQ HΨ
  sspecialize HΨ (y + 1) hP HQ
  sexact HΨ

end specialize

namespace cases

theorem rename (P : SPred σs) : P ⊢ₛ P := by
  sintro HP
  scases HP with HP'
  sexact HP'

theorem clear (P Q : SPred σs) : ⊢ₛ P → Q → P := by
  sintro HP HQ
  scases HQ with -
  sexact HP

theorem pure (P : SPred σs) (Q : Prop) : φ → (⊢ₛ P → ⌜Q⌝ → P) := by
  intro hφ
  sintro HP HQ
  scases HQ with ⌜hQ⌝
  sexact HP

theorem riddle (P : SPred σs) (Q : Prop) (hqr : Q → ⊢ₛ R) : ⊢ₛ P → ⌜Q⌝ → R := by
  sintro HP HQ
  scases HQ with ⌜hQ⌝
  have hr : ⊢ₛ R := hqr hQ
  apply SPred.true_intro.trans hr

theorem and (P Q R : SPred σs) : (P ∧ Q ∧ R) ⊢ₛ R := by
  sintro HPQR
  scases HPQR with ⟨HP, HQ, HR⟩
  sexact HR

theorem and_clear_pure (P Q R : SPred σs) (φ : Prop) : (P ∧ Q ∧ ⌜φ⌝ ∧ R) ⊢ₛ R := by
  sintro HPQR
  scases HPQR with ⟨_, -, ⌜hφ⌝, HR⟩
  sexact HR

theorem or (P Q R : SPred σs) : P ∧ (Q ∨ R) ∧ (Q → R) ⊢ₛ R := by
  sintro H
  scases H with ⟨-, ⟨HQ | HR⟩, HQR⟩
  · sspecialize HQR HQ
    sexact HQR
  · sexact HR

end cases

/-
TODO:
- rcases
- intro
- exfalso?
- sexact with pure hypothesis (SPred.true_intro.trans h)
-/
