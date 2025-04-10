import MPL.ProofMode

open MPL

variable (σs : List Type)

theorem start_stop (Q : SProp σs) (H : Q ⊢ₛ Q) : Q ⊢ₛ Q := by
  sstart
  sintro HQ
  sstop
  exact H

theorem exact (Q : SProp σs) : Q ⊢ₛ Q := by
  sstart
  sintro HQ
  sexact HQ

theorem clear (P Q : SProp σs) : P ⊢ₛ Q → Q := by
  sintro HP
  sintro HQ
  sclear HP
  sexact HQ

theorem assumption (P Q : SProp σs) : Q ⊢ₛ P → Q := by
  sintro _ _
  sassumption

namespace pure

theorem move (Q : SProp σs) : ⌜φ⌝ ⊢ₛ Q → Q := by
  sintro Hφ
  sintro HQ
  spure Hφ
  sexact HQ

theorem move_multiple (Q : SProp σs) : ⌜φ₁⌝ ⊢ₛ ⌜φ₂⌝ → Q → Q := by
  sintro Hφ1
  sintro Hφ2
  sintro HQ
  spure Hφ1
  spure Hφ2
  sexact HQ

theorem move_conjunction (Q : SProp σs) : (⌜φ₁⌝ ∧ ⌜φ₂⌝) ⊢ₛ Q → Q := by
  sintro Hφ
  sintro HQ
  spure Hφ
  sexact HQ

end pure

namespace pureintro

theorem simple : ⊢ₛ (⌜True⌝ : SProp σs) := by
  spure_intro
  exact True.intro

theorem or : ⊢ₛ ⌜True⌝ ∨ (⌜False⌝ : SProp σs) := by
  spure_intro
  left
  exact True.intro

theorem with_proof (H : A → B) (P Q : SProp σs) : P ⊢ₛ Q → ⌜A⌝ → ⌜B⌝ := by
  sintro _HP _HQ
  spure_intro
  exact H

end pureintro

namespace constructor

theorem and (Q : SProp σs) : Q ⊢ₛ Q ∧ Q := by
  sintro HQ
  sconstructor
  <;> sexact HQ

end constructor

namespace leftright

theorem left (P Q : SProp σs) : P ⊢ₛ P ∨ Q := by
  sintro HP
  sleft
  sexact HP

theorem right (P Q : SProp σs) : Q ⊢ₛ P ∨ Q := by
  sintro HQ
  sright
  sexact HQ

theorem complex (P Q R : SProp σs) : ⊢ₛ P → Q → P ∧ (R ∨ Q ∨ R) := by
  sintro HP HQ
  sconstructor
  · sassumption
  sright
  sleft
  sexact HQ

end leftright

namespace specialize

theorem simple (P Q : SProp σs) : P ⊢ₛ (P → Q) → Q := by
  sintro HP HPQ
  sspecialize HPQ HP
  sexact HPQ

end specialize

/-
TODO:
- rcases
- intro
- specialize
-/
