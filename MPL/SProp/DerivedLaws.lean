import MPL.SProp.Laws

namespace MPL.SProp

variable {σs : List Type} {P P' Q Q' R R' : SProp σs} {φ φ₁ φ₂ : Prop}

/- Most of the laws below are derived from the laws in Laws.lean
and should not need induction on σs. TODO: Realize this or move to Laws.lean. -/

theorem entails.rfl {σs : List Type} {P : SProp σs} : P ⊢ₛ P := entails.refl P

theorem bientails.rfl {σs : List Type} {P : SProp σs} : P ⊣⊢ₛ P := bientails.refl P
theorem bientails.of_eq {σs : List Type} {P Q : SProp σs} (h : P = Q) : P ⊣⊢ₛ Q := h ▸ .rfl

theorem bientails.mp {σs : List Type} {P Q : SProp σs} : (P ⊣⊢ₛ Q) → (P ⊢ₛ Q) := fun h => (bientails.iff.mp h).1
theorem bientails.mpr {σs : List Type} {P Q : SProp σs} : (P ⊣⊢ₛ Q) → (Q ⊢ₛ P) := fun h => (bientails.iff.mp h).2

/-! # Connectives -/

theorem and_elim_l' (h : P ⊢ₛ R) : P ∧ Q ⊢ₛ R := and_elim_l.trans h
theorem and_elim_r' (h : Q ⊢ₛ R) : P ∧ Q ⊢ₛ R := and_elim_r.trans h
theorem or_intro_l' (h : P ⊢ₛ Q) : P ⊢ₛ Q ∨ R := h.trans or_intro_l
theorem or_intro_r' (h : P ⊢ₛ R) : P ⊢ₛ Q ∨ R := h.trans or_intro_r
theorem and_symm : P ∧ Q ⊢ₛ Q ∧ P := and_intro and_elim_r and_elim_l
theorem or_symm : P ∨ Q ⊢ₛ Q ∨ P := or_elim or_intro_r or_intro_l
theorem imp_intro' (h : Q ∧ P ⊢ₛ R) : P ⊢ₛ Q → R := imp_intro <| and_symm.trans h
theorem mp (h1 : P ⊢ₛ Q → R) (h2 : P ⊢ₛ Q) : P ⊢ₛ R := (and_intro .rfl h2).trans (imp_elim h1)
theorem imp_elim' (h : Q ⊢ₛ P → R) : P ∧ Q ⊢ₛ R := and_symm.trans <| imp_elim h
theorem imp_elim_l : (P → Q) ∧ P ⊢ₛ Q := imp_elim .rfl
theorem imp_elim_r : P ∧ (P → Q) ⊢ₛ Q := imp_elim' .rfl
theorem false_elim : ⌜False⌝ ⊢ₛ P := pure_elim' False.elim
theorem true_intro : P ⊢ₛ ⌜True⌝ := pure_intro trivial
theorem exists_intro' {Ψ : α → SProp σs} (a : α) (h : P ⊢ₛ Ψ a) : P ⊢ₛ ∃ a, Ψ a := h.trans (exists_intro a)

/-! # Monotonicity and congruence -/

theorem and_mono (hp : P ⊢ₛ P') (hq : Q ⊢ₛ Q') : P ∧ Q ⊢ₛ P' ∧ Q' := and_intro (and_elim_l' hp) (and_elim_r' hq)
theorem and_mono_l (h : P ⊢ₛ P') : P ∧ Q ⊢ₛ P' ∧ Q := and_mono h .rfl
theorem and_mono_r (h : Q ⊢ₛ Q') : P ∧ Q ⊢ₛ P ∧ Q' := and_mono .rfl h
theorem and_congr (hp : P ⊣⊢ₛ P') (hq : Q ⊣⊢ₛ Q') : P ∧ Q ⊣⊢ₛ P' ∧ Q' := bientails.iff.mpr ⟨and_mono (bientails.mp hp) (bientails.mp hq), and_mono (bientails.mpr hp) (bientails.mpr hq)⟩
theorem and_congr_l (hp : P ⊣⊢ₛ P') : P ∧ Q ⊣⊢ₛ P' ∧ Q := and_congr hp .rfl
theorem and_congr_r (hq : Q ⊣⊢ₛ Q') : P ∧ Q ⊣⊢ₛ P ∧ Q' := and_congr .rfl hq
theorem or_mono (hp : P ⊢ₛ P') (hq : Q ⊢ₛ Q') : P ∨ Q ⊢ₛ P' ∨ Q' := or_elim (or_intro_l' hp) (or_intro_r' hq)
theorem or_mono_l (h : P ⊢ₛ P') : P ∨ Q ⊢ₛ P' ∨ Q := or_mono h .rfl
theorem or_mono_r (h : Q ⊢ₛ Q') : P ∨ Q ⊢ₛ P ∨ Q' := or_mono .rfl h
theorem or_congr (hp : P ⊣⊢ₛ P') (hq : Q ⊣⊢ₛ Q') : P ∨ Q ⊣⊢ₛ P' ∨ Q' := bientails.iff.mpr ⟨or_mono (bientails.mp hp) (bientails.mp hq), or_mono (bientails.mpr hp) (bientails.mpr hq)⟩
theorem or_congr_l (hp : P ⊣⊢ₛ P') : P ∨ Q ⊣⊢ₛ P' ∨ Q := or_congr hp .rfl
theorem or_congr_r (hq : Q ⊣⊢ₛ Q') : P ∨ Q ⊣⊢ₛ P ∨ Q' := or_congr .rfl hq
theorem imp_mono (h1 : Q ⊢ₛ P) (h2 : P' ⊢ₛ Q') : (P → P') ⊢ₛ Q → Q' := imp_intro <| (and_mono_r h1).trans <| (imp_elim .rfl).trans h2
theorem imp_mono_l (h : P' ⊢ₛ P) : (P → Q) ⊢ₛ (P' → Q) := imp_mono h .rfl
theorem imp_mono_r (h : Q ⊢ₛ Q') : (P → Q) ⊢ₛ (P → Q') := imp_mono .rfl h
theorem imp_congr (h1 : P ⊣⊢ₛ Q) (h2 : P' ⊣⊢ₛ Q') : (P → P') ⊣⊢ₛ (Q → Q') := bientails.iff.mpr ⟨imp_mono h1.mpr h2.mp, imp_mono h1.mp h2.mpr⟩
theorem imp_congr_l (h : P ⊣⊢ₛ P') : (P → Q) ⊣⊢ₛ (P' → Q) := imp_congr h .rfl
theorem imp_congr_r (h : Q ⊣⊢ₛ Q') : (P → Q) ⊣⊢ₛ (P → Q') := imp_congr .rfl h
theorem forall_mono {Φ Ψ : α → SProp σs} (h : ∀ a, Φ a ⊢ₛ Ψ a) : (∀ a, Φ a) ⊢ₛ ∀ a, Ψ a := forall_intro fun a => (forall_elim a).trans (h a)
theorem forall_congr {Φ Ψ : α → SProp σs} (h : ∀ a, Φ a ⊣⊢ₛ Ψ a) : (∀ a, Φ a) ⊣⊢ₛ ∀ a, Ψ a := bientails.iff.mpr ⟨forall_mono fun a => (h a).mp, forall_mono fun a => (h a).mpr⟩
theorem exists_mono {Φ Ψ : α → SProp σs} (h : ∀ a, Φ a ⊢ₛ Ψ a) : (∃ a, Φ a) ⊢ₛ ∃ a, Ψ a := exists_elim fun a => (h a).trans (exists_intro a)
theorem exists_congr {Φ Ψ : α → SProp σs} (h : ∀ a, Φ a ⊣⊢ₛ Ψ a) : (∃ a, Φ a) ⊣⊢ₛ ∃ a, Ψ a := bientails.iff.mpr ⟨exists_mono fun a => (h a).mp, exists_mono fun a => (h a).mpr⟩

/-! # Boolean algebra -/

theorem and_self : P ∧ P ⊣⊢ₛ P := bientails.iff.mpr ⟨and_elim_l, and_intro .rfl .rfl⟩
theorem or_self : P ∨ P ⊣⊢ₛ P := bientails.iff.mpr ⟨or_elim .rfl .rfl, or_intro_l⟩
theorem and_comm : P ∧ Q ⊣⊢ₛ Q ∧ P := bientails.iff.mpr ⟨and_symm, and_symm⟩
theorem or_comm : P ∨ Q ⊣⊢ₛ Q ∨ P := bientails.iff.mpr ⟨or_symm, or_symm⟩
theorem and_assoc : (P ∧ Q) ∧ R ⊣⊢ₛ P ∧ Q ∧ R := bientails.iff.mpr ⟨and_intro (and_elim_l' and_elim_l) (and_mono_l and_elim_r), and_intro (and_mono_r and_elim_l) (and_elim_r' and_elim_r)⟩
theorem or_assoc : (P ∨ Q) ∨ R ⊣⊢ₛ P ∨ Q ∨ R := bientails.iff.mpr ⟨or_elim (or_mono_r or_intro_l) (or_intro_r' or_intro_r), or_elim (or_intro_l' or_intro_l) (or_mono_l or_intro_r)⟩

theorem true_and : ⌜True⌝ ∧ P ⊣⊢ₛ P := bientails.iff.mpr ⟨and_elim_r, and_intro (pure_intro trivial) .rfl⟩
theorem and_true : P ∧ ⌜True⌝ ⊣⊢ₛ P := and_comm.trans true_and
theorem false_and : ⌜False⌝ ∧ P ⊣⊢ₛ ⌜False⌝ := bientails.iff.mpr ⟨and_elim_l, false_elim⟩
theorem and_false : P ∧ ⌜False⌝ ⊣⊢ₛ ⌜False⌝ := and_comm.trans false_and
theorem true_or : ⌜True⌝ ∨ P ⊣⊢ₛ ⌜True⌝ := bientails.iff.mpr ⟨true_intro, or_intro_l⟩
theorem or_true : P ∨ ⌜True⌝ ⊣⊢ₛ ⌜True⌝ := or_comm.trans true_or
theorem false_or : ⌜False⌝ ∨ P ⊣⊢ₛ P := bientails.iff.mpr ⟨or_elim false_elim .rfl, or_intro_r⟩
theorem or_false : P ∨ ⌜False⌝ ⊣⊢ₛ P := or_comm.trans false_or

theorem true_imp : (⌜True⌝ → P) ⊣⊢ₛ P := bientails.iff.mpr ⟨and_true.mpr.trans imp_elim_l, imp_intro and_elim_l⟩
theorem imp_self : Q ⊢ₛ P → P := imp_intro and_elim_r
theorem imp_trans : (P → Q) ∧ (Q → R) ⊢ₛ P → R := imp_intro' <| and_assoc.mpr.trans <| (and_mono_l imp_elim_r).trans imp_elim_r
theorem false_imp : (⌜False⌝ → P) ⊣⊢ₛ ⌜True⌝ := bientails.iff.mpr ⟨true_intro, imp_intro <| and_elim_r.trans false_elim⟩

/-! # Pure -/

theorem pure_elim {φ : Prop} (h1 : Q ⊢ₛ ⌜φ⌝) (h2 : φ → Q ⊢ₛ R) : Q ⊢ₛ R :=
  and_self.mpr.trans <| imp_elim <| h1.trans <| pure_elim' fun h =>
    imp_intro' <| and_elim_l.trans (h2 h)

theorem pure_mono {φ₁ φ₂ : Prop} (h : φ₁ → φ₂) : ⌜φ₁⌝ ⊢ₛ (⌜φ₂⌝ : SProp σs) := pure_elim' <| pure_intro ∘ h
theorem pure_congr {φ₁ φ₂ : Prop} (h : φ₁ ↔ φ₂) : ⌜φ₁⌝ ⊣⊢ₛ (⌜φ₂⌝ : SProp σs) := bientails.iff.mpr ⟨pure_mono h.1, pure_mono h.2⟩

theorem pure_elim_l {φ : Prop} (h : φ → Q ⊢ₛ R) : ⌜φ⌝ ∧ Q ⊢ₛ R := pure_elim and_elim_l <| and_elim_r' ∘ h
theorem pure_elim_r {φ : Prop} (h : φ → Q ⊢ₛ R) : Q ∧ ⌜φ⌝ ⊢ₛ R := and_comm.mp.trans (pure_elim_l h)
theorem pure_true {φ : Prop} (h : φ) : ⌜φ⌝ ⊣⊢ₛ (⌜True⌝ : SProp σs) := eq_true h ▸ .rfl
theorem pure_and {φ₁ φ₂ : Prop} : ⌜φ₁⌝ ∧ (⌜φ₂⌝ : SProp σs) ⊣⊢ₛ ⌜φ₁ ∧ φ₂⌝ := bientails.iff.mpr ⟨pure_elim and_elim_l fun h => and_elim_r' <| pure_mono <| And.intro h, and_intro (pure_mono And.left) (pure_mono And.right)⟩
theorem pure_or {φ₁ φ₂ : Prop} : ⌜φ₁⌝ ∨ (⌜φ₂⌝ : SProp σs) ⊣⊢ₛ ⌜φ₁ ∨ φ₂⌝ := bientails.iff.mpr ⟨or_elim (pure_mono Or.inl) (pure_mono Or.inr), pure_elim' (·.elim (or_intro_l' ∘ pure_intro) (or_intro_r' ∘ pure_intro))⟩
theorem pure_imp_2 {φ₁ φ₂ : Prop} : ⌜φ₁ → φ₂⌝ ⊢ₛ (⌜φ₁⌝ → ⌜φ₂⌝ : SProp σs) := imp_intro <| pure_and.mp.trans <| pure_mono (And.elim id)
theorem pure_imp {φ₁ φ₂ : Prop} : (⌜φ₁⌝ → ⌜φ₂⌝ : SProp σs) ⊣⊢ₛ ⌜φ₁ → φ₂⌝ := by
  refine bientails.iff.mpr ⟨?_, pure_imp_2⟩
  by_cases h : φ₁
  · exact (mp .rfl (pure_intro h)).trans (pure_mono fun h _ => h)
  · exact pure_intro h.elim

theorem pure_forall_2 {φ : α → Prop} : ⌜∀ x, φ x⌝ ⊢ₛ ∀ x, (⌜φ x⌝ : SProp σs) := forall_intro fun _ => pure_mono (· _)
theorem pure_forall {φ : α → Prop} : (∀ x, (⌜φ x⌝ : SProp σs)) ⊣⊢ₛ ⌜∀ x, φ x⌝ := by
  refine bientails.iff.mpr ⟨?_, pure_forall_2⟩
  by_cases h : ∃ x, ¬φ x
  · let ⟨x, h⟩ := h
    exact (forall_elim x).trans (pure_mono h.elim)
  · exact pure_intro fun x => Classical.not_not.1 <| mt (⟨x, ·⟩) h

theorem pure_exists {φ : α → Prop} : (∃ x, ⌜φ x⌝ : SProp σs) ⊣⊢ₛ ⌜∃ x, φ x⌝ := bientails.iff.mpr ⟨exists_elim fun a => pure_mono (⟨a, ·⟩), pure_elim' fun ⟨x, h⟩ => (pure_intro h).trans (exists_intro' x .rfl)⟩

/-! # Miscellaneous -/

theorem and_left_comm : P ∧ Q ∧ R ⊣⊢ₛ Q ∧ P ∧ R := and_assoc.symm.trans <| (and_congr_l and_comm).trans and_assoc
theorem and_right_comm : (P ∧ Q) ∧ R ⊣⊢ₛ (P ∧ R) ∧ Q := and_assoc.trans <| (and_congr_r and_comm).trans and_assoc.symm

/-! # Working with entailment -/

theorem entails_pure_intro {σs : List Type} (P Q : Prop) (h : P → Q) : ⌜P⌝.entails (σs := σs) ⌜Q⌝ := pure_elim' fun hp => pure_intro (h hp)

@[simp]
theorem entails_pure_elim {σ : Type} {σs : List Type} [Inhabited σ] (P Q : Prop) : ⌜P⌝.entails (σs := σ::σs) ⌜Q⌝ ↔ ⌜P⌝.entails (σs := σs) ⌜Q⌝:= by simp only [entails, idiom_cons, forall_const]

@[simp]
theorem entails_true_intro {σs : List Type} (P Q : SProp σs) : ⌜True⌝ ⊢ₛ P → Q ↔ P ⊢ₛ Q := by
  induction σs
  case nil => simp only [pure, idiom_nil, imp_nil, entails_nil, forall_const]
  case cons σ σs ih => simp only [entails, idiom_cons, imp, ih]
