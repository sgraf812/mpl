import Lean
import Mathlib

open Lean
open Lean.Parser
open Lean.Elab.Command
open Lean.Elab
open Lean.Elab.Tactic
open Lean.Meta
open Lean.SubExpr
--open Std.Range

section StateT

def StateT.le [base : ∀{α}, LE (w α)] : StateT σ w α → StateT σ w α → Prop :=
  fun x y => ∀s, x.run s ≤ y.run s
instance [base : ∀{α}, LE (w α)] : LE (StateT σ w α) := ⟨StateT.le⟩
instance [base : ∀{α}, Preorder (w α)] : Preorder (StateT σ w α) where
  le_refl := fun x => fun s => le_refl (x.run s)
  le_trans := fun x y z hxy hyz => fun s => (hxy s).trans (hyz s)
instance [base : ∀{α}, PartialOrder (w α)] : PartialOrder (StateT σ w α) where
  le_antisymm := fun _ _ hxy hyx => funext fun s => (hxy s).antisymm (hyx s)
-- instance [base : ∀{α}, SemilatticeSup (w α)] : SemilatticeSup (StateT σ w α) where
-- instance [base : ∀{α}, SemilatticeInf (w α)] : SemilatticeInf (StateT σ w α) where
-- instance [base : ∀{α}, Lattice (w α)] : Lattice (StateT σ w α) where
-- instance [base : ∀{α}, CompleteLattice (w α)] : CompleteLattice (StateT σ w α) where

end StateT

section LawfulMonadState

class LawfulMonadState (σ : semiOutParam (Type u)) (m : Type u → Type v) [Monad m] [LawfulMonad m] [MonadStateOf σ m] where
  get_set : (do let s ← get; set s) = pure (f := m) ⟨⟩
  set_get {k : σ → m β} : (do set s₁; let s₂ ← get; k s₂) = (do set s₁; k s₁)
  set_set {s₁ s₂ : σ} : (do set s₁; set s₂) = set (m := m) s₂

theorem LawfulMonadState.set_get_pure [Monad m] [LawfulMonad m] [MonadStateOf σ m] [LawfulMonadState σ m] {s : σ} :
  (do set s; get) = (do set (m := m) s; pure s) := by
    calc (do set s; get)
      _ = (do set s; let s' ← get; pure s') := by simp
      _ = (do set s; pure s) := by rw [LawfulMonadState.set_get]
attribute [simp] LawfulMonadState.get_set LawfulMonadState.set_get LawfulMonadState.set_set LawfulMonadState.set_get_pure

instance [Monad m] [LawfulMonad m] : LawfulMonadState σ (StateT σ m) where
  get_set := by ext s; simp
  set_get := by intros; ext s; simp
  set_set := by intros; ext s; simp

end LawfulMonadState

section PredTrans

def Loc : Type := Nat
instance : DecidableEq Loc := instDecidableEqNat

def AList.lookupDefault {α : Type u} [DecidableEq α] (xs : AList (fun (_ : α) => Type v)) (a : Type v) (l : α) : Type v :=
  match xs.lookup l with
  | some b => b
  | none => a

def Dyn.{u} : Type (u + 1) := Sigma (fun α => α)
def Heap.{u} : Type (u + 1) := AList (fun (_ : Loc) => Dyn)

def Heap.dom (μ : Heap) := μ.keys

def Heap.entries (μ : Heap) := AList.entries μ

def Heap.lookup (μ : Heap) (l : Loc) : Option Dyn :=
  AList.lookup l μ

theorem Option.cast_none {α β : Type u} (h : α = β) : h ▸ (none : Option α) = (none : Option β) := by
  cases h
  rfl

theorem Option.cast_none_ne_some (h : α = β) : h ▸ (none : Option α) = some x → False := by
  simp[Option.cast_none]

def Heap.empty : Heap := (∅ : AList _)

instance : EmptyCollection Heap where
  emptyCollection := Heap.empty

instance : Inhabited Heap where
  default := Heap.empty

def Heap.mem : Heap → Loc → Prop :=
  fun μ l => l ∈ μ.dom

instance : Membership Loc Heap where
  mem := Heap.mem

def Heap.Disjoint : Heap → Heap → Prop :=
  fun μ₁ μ₂ => ∀ l, l ∈ μ₁.dom → l ∉ μ₂.dom

def Heap.union : Heap → Heap → Heap :=
  fun μ₁ μ₂ => AList.union μ₁ μ₂

instance : Union Heap where
  union := Heap.union

def Heap.single : Loc → Dyn → Heap := AList.singleton

@[simp]
theorem Heap.empty_union : Heap.empty ∪ μ = μ := by
  simp only [Union.union, union, empty]
  exact AList.empty_union

@[simp]
theorem Heap.union_empty : μ ∪ Heap.empty = μ := by
  simp only [Union.union, union, empty]
  exact AList.union_empty

def Heap.le (μ₁ μ₂ : Heap) :=
  μ₁.entries ⊆ μ₂.entries

instance Heap.instLE : LE Heap where
  le := Heap.le

instance Heap.instPreorder : Preorder Heap where
  le_refl := by simp only [LE.le, le, List.Subset.refl, implies_true]
  le_trans := fun _ _ _ hab hbc => List.Subset.trans hab hbc

@[simp]
theorem Heap.empty_bot : Heap.empty ≤ μ := by
  simp only [LE.le, le, entries, empty, EmptyCollection.emptyCollection, List.nil_subset]

def HProp : Type (u + 1) := Heap.{u} → Prop

@[ext]
theorem HProp.ext {p q : HProp} (h : ∀ μ, p μ = q μ) : p = q := funext h

def HProp.implies (p q : HProp) :=
  ∀ μ, p μ → q μ

instance HProp.instLE : LE HProp where
  le := HProp.implies

instance HProp.instPreorder : Preorder HProp where
  le_refl := by simp only [LE.le, implies, imp_self, implies_true]
  le_trans := fun _ _ _ hab hbc μ => hbc μ ∘ hab μ

instance HProp.instPartialOrder : PartialOrder HProp where
  le_antisymm := by
    intro _ _ hab hba
    ext μ
    constructor
    · exact hab μ
    · exact hba μ

def HProp.empty : HProp :=
  (· = Heap.empty)

set_option pp.universes true in
def HProp.single (l : Loc) (a : α) : HProp := fun μ =>
  μ.lookup l = some (Sigma.mk α a)

def HProp.sep_conj (p q : HProp) : HProp := fun μ =>
  ∃ (μ₁ μ₂ : Heap), Heap.Disjoint μ₁ μ₂ ∧ μ₁ ∪ μ₂ = μ ∧ p μ₁ ∧ q μ₂

def HProp.exists (p : α → HProp) : HProp := fun μ =>
  ∃ a, p a μ

def HProp.forall (p : α → HProp) : HProp := fun μ =>
  ∀ a, p a μ

notation "emp" => HProp.empty
notation l "↦" a => HProp.single l a
notation:70 p:69 " ⋆ " q:70 => HProp.sep_conj p q
notation "∃' " x ", " p => HProp.exists (fun x => p)
notation "∃' " h " : " x ", " p => HProp.exists (fun (h : x) => p)
notation "∀' " x ", " p => HProp.forall (fun x => p)
notation "∀' " h " : " x ", " p => HProp.forall (fun (h : x) => p)

-- The remaining ones can be derived from the above:

def HProp.persistent (p : Prop) : HProp :=
  ∃' (_ : p), emp

-- The following instance is not a good idea, because
-- it is crucial that we are precise about the location where we coerce.
-- For example, `↑(p * q ⊢ h)` is very different to `p * ↑(q ⊢ h)`, yet
-- the latter is what we get if we just coerce the proposition `p * q ⊢ h`.
-- instance HProp.instCoe : Coe Prop (HProp Γ) where
--   coe := HProp.persistent
notation:max "↟" p:max => HProp.persistent p

def HProp.true : HProp :=
  ∃' (h : HProp), h

def HProp.sep_imp (p q : HProp) : HProp :=
  ∃' (h : HProp), h ⋆ ↟(p ⋆ q ≤ h)

notation:67 p " -⋆ " q => HProp.sep_imp p q

theorem HProp.op_comm {op : HProp → HProp → HProp} :
  (∀ p₁ p₂, op p₁ p₂ ≤ op p₂ p₁) →
  (∀ p₁ p₂, op p₁ p₂ = op p₂ p₁) := by
  intro h p₁ p₂
  exact le_antisymm (h p₁ p₂) (h p₂ p₁)

@[simp]
theorem HProp.empty_empty : emp μ ↔ μ = Heap.empty := Iff.intro (fun h => h) (fun h => h)

@[simp]
theorem HProp.persistent_intro : ↟p μ ↔ p ∧ μ = Heap.empty :=
  Iff.intro  (fun ⟨hp, he⟩ => ⟨hp, HProp.empty_empty.mp he⟩) (fun h => h.2 ▸ ⟨h.1, rfl⟩)

@[simp]
theorem HProp.single_intro : (l ↦ x) μ ↔ μ = Heap.single l (Sigma.mk _ x) :=
  sorry

@[simp]
theorem HProp.exists_exists : (HProp.exists p) μ ↔ ∃ x, p x μ := by
  simp only [«exists», imp_self]

@[simp]
theorem HProp.imp_exists_left : (HProp.exists p) ≤ q ↔ (∀ x, p x ≤ q) := by
  constructor
  · intro h x μ hp; exact h μ ⟨x, hp⟩
  · intro h μ ⟨x, hx⟩; exact h x μ hx

-- Did not manage to prove p ≤ (HProp.exists q) → (∃ x, p ≤ q x) because x may not depend on μ
theorem HProp.imp_exists_right : (p ≤ q x) → p ≤ (HProp.exists q) := by
  intro h μ hp
  exact ⟨x, h μ hp⟩

@[simp]
theorem HProp.persistent_true_eq_empty : ↟True = emp := by
  ext μ
  simp only [persistent, exists_exists, empty_empty, exists_const]

@[simp]
theorem HProp.persistent_implies_left {p : Prop} {q' : HProp} : ↟p ≤ q' ↔ (p ≤ q' Heap.empty) := by
  constructor
  · intro h hp
    exact h Heap.empty (by simp[hp])
  · intro h μ
    simp
    intro hp hμ
    exact hμ ▸ h hp

-- Reverse direction not provable
theorem HProp.persistent_implies_right {p' : HProp} : p' ≤ ↟q → (p' Heap.empty ≤ q) := by
  intro h hp
  have := h Heap.empty hp
  simp only [persistent_intro, and_true] at this
  exact this

@[simp]
theorem HProp.sep_conj_intro : (p ⋆ q) μ ↔ ∃ μ₁ μ₂, p μ₁ ∧ q μ₂ ∧ Heap.Disjoint μ₁ μ₂ ∧ μ = μ₁ ∪ μ₂ := by
  constructor
  · sorry
  · sorry

@[simp]
lemma HProp.forall_forall : (HProp.forall p) μ ↔ ∀ x, p x μ := sorry

@[simp]
lemma HProp.sep_imp_intro : (HProp.sep_imp p q) μ ↔ ∀ μ', Heap.Disjoint μ μ' → p μ' → q (μ ∪ μ') := sorry

@[simp]
theorem HProp.sep_conj_exists {p : α → HProp} : (∃' x, p x) ⋆ q = ∃' x, (p x ⋆ q) := by
  ext μ
  simp [HProp.exists, HProp.sep_conj]
  constructor
  · intro h
    rcases h with ⟨μ₁, μ₂, hdis, hunion, hp, hq⟩
    obtain ⟨a, hp⟩ := hp
    exact ⟨a, μ₁, μ₂, hdis, hunion, hp, hq⟩
  · intro h
    rcases h with ⟨a, μ₁, μ₂, hdis, hunion, hp, hq⟩
    exact ⟨μ₁, μ₂, hdis, hunion, ⟨a, hp⟩, hq⟩

@[simp]
theorem HProp.persistent_sep_conj : (↟p ⋆ q) μ ↔ p ∧ q μ := by
  simp[HProp.persistent]
  constructor
  · intro h
    obtain ⟨μ', hq⟩ := h
    sorry
  · sorry

def PredTrans.Pre (α : Type u) : Type (u + 1) :=
  (α → HProp.{u}) → HProp.{u}

@[simp]
theorem tmp {γ : Type v} {β : α → γ → Type v} {a : α} {f : (c : γ) → β a c} (h : a = b) {arg : γ} :
  Eq.recOn (motive := fun x x_1 => (c : γ) → β x c) h f arg = Eq.recOn h (f arg) := by
  cases h
  rfl

@[simp]
theorem tmp2 {β : α → Type v} {γ : α → Type v} {a : α} {f : γ a → β a} (h : a = b) {arg : γ b} :
  Eq.recOn (motive := fun x x_1 => γ x → β x) h f arg = Eq.recOn h (f (h ▸ arg)) := by
  cases h
  rfl

@[ext]
def PredTrans.Pre.ext {a b : PredTrans.Pre α} : (∀ p, a p = b p) → a = b := by
  simp[PredTrans.Pre]
  intro h
  ext p : 1
  exact h p

def PredTrans.Mono (t : PredTrans.Pre α) : Prop :=
  ∀ p q, p ≤ q → t p ≤ t q

def PredTrans.Frame (t : PredTrans.Pre α) : Prop :=
  ∀ μ₁ μ₂ p, Heap.Disjoint μ₁ μ₂ → t p μ₁ → t (fun a => p a ⋆ (· = μ₂)) (μ₁ ∪ μ₂)

structure PredTrans (α : Type u) : Type (u + 1) where
  trans : PredTrans.Pre α
  mono : PredTrans.Mono trans
  frame : PredTrans.Frame trans

@[ext]
def PredTrans.ext {a b : PredTrans α} : (∀ p, a.trans p = b.trans p) → a = b := by
  sorry  -- recover from history

def PredTrans.post (post : α → HProp) : PredTrans α :=
  { trans := fun p => ∀' a, post a -⋆ p a -- sep_imp on post conditions
    mono := by
      intro _ _ hpq μ hp
      simp_all
      intro x μ' hdis hpost
      exact hpq x (μ ∪ μ') (hp x μ' hdis hpost)
    frame := by
      intro μ₁ μ₂ p _hdis hp
      simp_all
      intro x μ' hdis hpost
      use (μ₁ ∪ μ')
      constructor
      · apply hp _ _ _ hpost
        show μ₁.Disjoint μ'; sorry
      · show (μ₁ ∪ μ').Disjoint μ₂ ∧ μ₁ ∪ μ₂ ∪ μ' = μ₁ ∪ μ' ∪ μ₂; sorry
  }

/-- Construct a PredTrans from a (single) postcondition of a (single) trace.
Note that not every PredTrans can be constructed this way, but all the
PredTrans that arise from deterministic programs can be represented this way.
Cousot calls PredTrans proper a "program property" (in Set(Set(α))), whereas
a the range of post characterizes the "trace properties" (in Set(α)).
Program properties are traditionally called hyperproperties, and PredTrans
is able to express all hyperproperties.
In fact, this function is exactly the "lift" combinator from the original
"hyperproperties" paper by Clarkson and Schneider that lifts a trace
property into a program property.
There is this paper about "Hyper Hoare Logic" discussing how Hoare triples
can be generalized to hyperproperties: https://dl.acm.org/doi/10.1145/3656437
-/
def PredTrans.persistent (post : α → Prop) : PredTrans α :=
  PredTrans.post (fun a => ↟(post a))

@[simp]
theorem PredTrans.persistent_elim : (PredTrans.persistent p).trans q μ ↔ (∀ a, p a → q a μ) := by
  simp_all[PredTrans.persistent, PredTrans.post]
  constructor
  · intro h a hp
    have := h a Heap.empty sorry hp rfl
    simp[this]
  · intro hpq a _ _ hp _
    exact hpq a hp

def PredTrans.le (a b : PredTrans α) :=
  ∀ p, b.trans p ≤ a.trans p

instance PredTrans.instLE : LE (PredTrans α) where
  le := PredTrans.le

instance PredTrans.instPreorder : Preorder (PredTrans α) where
  le_refl a := by
    intro p
    apply le_refl
  le_trans a b c hab hbc := by
    intro p
    apply le_trans (hbc p) (hab p)

instance PredTrans.instPartialOrder : PartialOrder (PredTrans α) where
  le_antisymm a b hab hba := by
    ext p : 1
    apply le_antisymm (hba p) (hab p)

theorem PredTrans.sep_conj_stuff {t : PredTrans α} : (t.trans p ⋆ (· = μ₂)) ≤ t.trans (fun a => p a ⋆ (· = μ₂)) := by
  intro μ
  simp
  intro μ₁ hp hdis hunion
  apply hunion ▸ t.frame μ₁ μ₂ _ hdis hp

def PredTrans.pure (a : α) : PredTrans α :=
  PredTrans.persistent (· = a)

def PredTrans.bind {α β} (x : PredTrans α) (f : α → PredTrans β) : PredTrans β :=
  { trans := fun p => x.trans (fun a => (f a).trans p),
    mono := fun _ _ hpq => x.mono _ _ (fun a => (f a).mono _ _ hpq),
    frame := by
      intro μ₁ μ₂ p _hdis hp
      have := x.frame μ₁ μ₂ _ _hdis hp
      apply x.mono (fun a => (f a).trans p ⋆ fun x => x = μ₂) (fun a => (f a).trans fun a => p a ⋆ fun x => x = μ₂) _ _ this
      intro a
      simp[PredTrans.sep_conj_stuff]
  }

instance PredTrans.instMonad : Monad PredTrans where
  pure := PredTrans.pure
  bind := PredTrans.bind

instance PredTrans.instLawfulMonad : LawfulMonad PredTrans where
  bind_pure_comp := by simp[Bind.bind, Pure.pure, Functor.map, Function.comp_def]
  pure_bind := by intros; ext p; simp[Bind.bind, Pure.pure, PredTrans.bind, PredTrans.pure]
  bind_assoc := by intros; ext p; simp [Bind.bind, PredTrans.bind]
  bind_map := by intros; ext p; simp [Bind.bind, PredTrans.bind, Functor.map, Function.comp_apply, PredTrans.pure, Seq.seq]
  map_pure := by intros; ext p; simp [Bind.bind, PredTrans.bind, Pure.pure, PredTrans.pure, Functor.map, Function.comp_apply]
  map_const := sorry
  id_map := sorry
  pure_seq := sorry
  seqLeft_eq := sorry
  seqRight_eq := sorry

-- Do we really want this as a simp rule?
@[simp]
theorem PredTrans.pure_of_persistent {α} {x : α} : PredTrans.persistent (· = x) = Pure.pure x := by
  simp only [Pure.pure, pure]

@[simp]
theorem PredTrans.persistent_mono : PredTrans.persistent p ≤ PredTrans.persistent q ↔ p ≤ q := by
  sorry
--  constructor
--  case mp =>
--    intro hqp
--    simp only [persistent, le_Prop_eq] at hqp
--    replace hqp := hqp q
--    simp at hqp
--    exact hqp
--  case mpr =>
--    intro hpq
--    intro x
--    simp only [post, le_Prop_eq]
--    intro hpx
--    exact le_trans hpq hpx


@[simp]
theorem PredTrans.post_mono : PredTrans.post p ≤ PredTrans.post q ↔ p ≤ q := by
  sorry
-- @[simp]
-- theorem PredTrans.pure_post_mono {α} {x : α} {p : α → Prop} : PredTrans.post p ≤ Pure.pure x ↔ ∀ y, p y → y = x := by
--   simp only [← pure_of_post, post_mono]

-- for general PredTrans, it seems we cannot prove the equivalence
-- theorem PredTrans.post_elim {w : PredTrans Prop α} : w ≤ PredTrans.post p → w.val p :=
--   fun h => h p (le_refl p)

@[simp]
theorem PredTrans.le_pure_post {α} {x : α} {p : α → Prop} : Pure.pure x ≤ PredTrans.persistent p ↔ p x := by
  simp[← PredTrans.pure_of_persistent, PredTrans.persistent_elim]

-- Just for future reference
-- example : PredTrans.post p ≤ Pure.pure x → p ≤ (· = x) := by
--   simp[←PredTrans.pure_of_post]
--   intros h
--   intro y
--   exact h y

@[simp]
theorem PredTrans.map_post {f : α → β} {t : PredTrans α} : (f <$> t).trans p = t.trans (fun a => p (f a)) := by
  sorry
  -- simp only [Functor.map, bind, Function.comp_apply, pure, persistent, post]

@[simp]
theorem PredTrans.le_map_post {f : α → β} : f <$> t ≤ PredTrans.persistent p ↔ t ≤ PredTrans.persistent (fun a => p (f a)) :=
  sorry
--   ⟨fun h _ hq => t.property _ _ hq (PredTrans.map_post ▸ h p (le_refl _)),
--    fun h _ hq => t.property _ _ (fun a => hq (f a)) (post_elim h)⟩

@[simp]
theorem PredTrans.post_bind_pure {f : α → β} : f <$> PredTrans.persistent p = PredTrans.persistent (fun b => ∃ a, f a = b ∧ p a) := by
  sorry
--   ext q
--   simp only [Bind.bind, bind, post, pure]
--   constructor
--   case mpr =>
--     intro h a hp
--     exact h (f a) ⟨a, rfl, hp⟩
--   case mp =>
--     intro h b ⟨a, hfa, hp⟩
--     exact hfa ▸ h a hp

theorem PredTrans.bind_persistent {f : α → PredTrans β} {goal : PredTrans β}
  (hgoal : ∀ a, p a → f a ≤ goal) : PredTrans.persistent p >>= f ≤ goal :=
  sorry
  -- fun q μ hq a hp => hgoal a hp q μ hq

@[simp]
theorem PredTrans.post_le_post_post : (PredTrans.persistent p).trans (fun a => HProp.persistent (q a)) Heap.empty ↔ PredTrans.persistent p ≤ PredTrans.persistent q := by
  sorry
--   simp[PredTrans.post]
--   constructor
--   · intro hpq r hqr
--     exact hpq.trans hqr
--   · intro h a hp
--     have := h q
--     simp at this
--     exact this a hp

-- theorem PredTrans.PredTrans_persistent_post :
--   ((PredTrans.persistent p).trans (fun a => HProp.persistent (q a)) Heap.empty)
--   ↔ (PredTrans.post p).trans q := by
--   simp[PredTrans.persistent_elim]

-- def PredTrans.toSep (x : PredTrans α) : PredTrans α :=
--   { trans := fun q μ => (x.val (fun a => q a μ)),
--     mono := by intro _ _ hpq μ; simp; exact x.property _ _ (fun a => hpq a μ)
--     frame := by
--       intro μ₁ μ₂ p hdis
--       simp_all
--       intro hp
--       apply x.property _ _ _ hp
--       intro a hp
--       use μ₁
--   }

-- theorem PredTrans.PredTrans_pure_pure :
--   PredTrans.pure x = PredTrans.toSep (PredTrans.pure x) := by
--   ext p μ
--   simp only [pure, persistent_elim, forall_eq, PredTrans.toSep, PredTrans.pure]

-- theorem PredTrans.PredTrans_bind_bind :
--   PredTrans.bind (PredTrans.toSep x) (fun a => PredTrans.toSep (f a))
--   = PredTrans.toSep (PredTrans.bind x f) := by
--   simp[PredTrans.bind, PredTrans.bind, PredTrans.toSep]

end PredTrans

section MonadOrdered

class MonadOrdered (w : Type u → Type v) [∀{α},Preorder (w α)] extends Monad w, LawfulMonad w where
  -- the following theorem combines
  -- * substitutivity (x ≤ y → x >>= f ≤ y >>= f)
  -- * congruence (f ≤ g → x >>= f ≤ x >>= g)
  bind_mono : ∀{α β} {x y : w α} {f g : α → w β}, x ≤ y → f ≤ g → x >>= f ≤ y >>= g

theorem MonadOrdered.map_mono {w : Type u → Type v} {f : α → β} {x y : w α} [∀{α}, Preorder (w α)] [MonadOrdered w]
  (h : x ≤ y) : f <$> x ≤ f <$> y := by simp only [← bind_pure_comp, le_refl, bind_mono h]

theorem MonadOrdered.seq_mono {w : Type u → Type v} {f g : w (α → β)} {x y : w α} [∀{α}, Preorder (w α)] [MonadOrdered w]
  (h₁ : f ≤ g) (h₂ : x ≤ y) : f <*> x ≤ g <*> y := by
  simp only [← bind_map, ← bind_pure_comp]
  exact bind_mono h₁ (fun a => bind_mono h₂ (by rfl))

attribute [simp] MonadOrdered.bind_mono MonadOrdered.map_mono MonadOrdered.seq_mono

theorem MonadOrdered.bind_mono_sup {w : Type u → Type v} {x y : w α} {f : α → w β} [∀{α}, SemilatticeSup (w α)] [MonadOrdered w] :
  (x >>= f) ⊔ (y >>= f) ≤ x ⊔ y >>= f:= by
  have hx : x >>= f ≤ x ⊔ y >>= f := MonadOrdered.bind_mono le_sup_left (le_refl f)
  have hy : y >>= f ≤ x ⊔ y >>= f := MonadOrdered.bind_mono le_sup_right (le_refl f)
  exact sup_le hx hy

instance PredTrans.instMonadOrdered : MonadOrdered PredTrans where
  bind_mono := by
    intros _ _ x y f g hxy hfg
    simp[Bind.bind,PredTrans.bind] at *
    intro p μ h
    apply hxy
    exact y.mono _ _ (fun a => hfg a p) μ h

instance StateT.instMonadOrdered [∀{α}, Preorder (w α)] [MonadOrdered w] : MonadOrdered (StateT σ w) where
  bind_mono := by
    intros _ _ _ _ _ _ hxy hfg
    intro s
    simp
    apply MonadOrdered.bind_mono
    apply hxy
    intro p;
    apply hfg

end MonadOrdered

section Observation

class Observation (m : Type u → Type v) (w : outParam (Type u → Type x)) [Monad m] [∀{α}, Preorder (w α)] extends MonadOrdered w where
  observe : m α → w α
  pure_pure : observe (Pure.pure a) = Pure.pure a
  bind_bind (x : m α) (f : α → m β) : observe (x >>= f) = observe x >>= (fun a => observe (f a))
open Observation (observe)

theorem Observation.map_map {m : Type u → Type v} {w : Type u → Type x} [Monad m] [LawfulMonad m] [∀{α}, Preorder (w α)] [Observation m w] {f : α → β} {x : m α} :
  observe (f <$> x) = f <$> observe (w:=w) x := by simp only [← bind_pure_comp, bind_bind, pure_pure]
theorem Observation.seq_seq {m : Type u → Type v} {w : Type u → Type x} [Monad m] [LawfulMonad m] [∀{α}, Preorder (w α)] [Observation m w] {f : m (α → β)} {x : m α} :
  observe (f <*> x) = observe f <*> observe (w:=w) x := by simp only [← bind_map, bind_bind, map_map]
attribute [simp] Observation.pure_pure Observation.bind_bind Observation.map_map Observation.seq_seq

class ObservationState (σ : Type u) (m : Type u → Type v) (w : Type u → Type x) [∀{α}, Preorder (w α)] [Monad m] [MonadStateOf σ m] extends MonadStateOf σ w, Observation m w where
  get_get : observe MonadState.get = MonadState.get
  set_set : observe (MonadStateOf.set s) = MonadStateOf.set (σ := σ) s
attribute [simp] ObservationState.get_get ObservationState.set_set

instance StateT.instObservationState [Monad m] [∀{α}, Preorder (w α)] [base : Observation m w] :
  ObservationState σ (StateT σ m) (StateT σ w) where
  observe := fun x s₁ => base.observe (x.run s₁)
  pure_pure := by
    intros _ a
    ext s
    simp[StateT.run,Pure.pure,StateT.pure,base.pure_pure]
  bind_bind := by
    intros _ _ x f
    ext s
    simp[StateT.run,Bind.bind,StateT.bind,base.bind_bind]
  get_get := by
    ext s
    simp[StateT.run, MonadState.get, getThe, MonadStateOf.get, StateT.get]
  set_set := by
    intro s
    ext s'
    simp[StateT.run, MonadStateOf.set, StateT.set]

def Except.le [LE ε] [LE α] (x : Except ε α) (y : Except ε α) :=
  match x, y with
  | Except.error _, Except.ok _ => True
  | Except.error x, Except.error y => x ≤ y
  | Except.ok _, Except.error _ => False
  | Except.ok x, Except.ok y => x ≤ y
instance Except.instLE [LE ε] [LE α] : LE (Except ε α) where
  le := Except.le
instance Except.instPreorder [Preorder ε] [Preorder α] : Preorder (Except ε α) where
  le_refl := fun x => by cases x <;> simp[LE.le, Except.le]
  le_trans := fun x y z hxy hyz => by
    simp[LE.le, Except.le] at hxy hyz
    cases x <;> cases y <;> cases z <;> simp[LE.le, Except.le, hxy, hyz]
    simp_all
    · exact le_trans hxy hyz
    · simp at *
    · simp at *
    · exact le_trans hxy hyz

def ExceptT.le [∀{α}, LE (w α)] (a b : ExceptT ε w α) :=
  ExceptT.run a ≤ ExceptT.run b
instance ExceptT.instLE [∀{α}, Preorder (w α)] : LE (ExceptT ε w α) where
  le := ExceptT.le
instance ExceptT.instPreorder [∀{α}, Preorder (w α)] : Preorder (ExceptT ε w α) where
  le_refl := fun x => le_refl (ExceptT.run x)
  le_trans := by intro _ _ _ hxy hyz; simp [LE.le, le] at *; exact le_trans hxy hyz

instance ExceptT.instMonadOrdered [∀{α}, Preorder (w α)] [MonadOrdered w] : MonadOrdered (ExceptT ε w) where
  bind_mono := by
    intro _ _ _ _ _ _ hxy hfg
    simp only [LE.le, le, bind, ExceptT.bind, run_mk]
    apply MonadOrdered.bind_mono
    · exact hxy
    · intro x
      cases x <;> simp only [ExceptT.bindCont, le_refl]
      apply hfg

def ExceptT.observe [Monad m] [Monad w] [∀{α}, Preorder (w α)] [base : Observation m w] (x : ExceptT ε m α) : ExceptT ε w α :=
  ExceptT.mk (base.observe (ExceptT.run x))

instance ExceptT.instObservation [Monad m] [∀{α}, Preorder (w α)] [base : Observation m w] :
  Observation (ExceptT ε m) (ExceptT ε w) where
  observe := fun x => base.observe (ExceptT.run x)
  pure_pure := base.pure_pure
  bind_bind := by
    intros _ _ x f
    have h : ExceptT.bindCont (ExceptT.observe ∘ f) = (base.observe ∘ ExceptT.bindCont f) := by
      ext x
      simp[ExceptT.bindCont,ExceptT.observe]
      split
      · rfl
      · simp only [base.pure_pure]
    calc (x >>= f).observe
      _ = mk (base.observe (x.run >>= ExceptT.bindCont f)) := rfl
      _ = mk (base.observe x.run >>= (base.observe ∘ ExceptT.bindCont f)) := by simp only [base.bind_bind, Function.comp_def]
      _ = mk (base.observe x.run >>= ExceptT.bindCont (observe ∘ f)) := by rw[h]
      _ = x.observe >>= (fun a => (f a).observe) := rfl

-- the following *might* be useful, but I haven't been able to apply it yet
theorem Observation.ForInStep_split {m : Type u → Type v} {w : Type u → Type x} {r : ForInStep β} {y d : β → m ρ}
  [Monad m] [∀{α}, Preorder (w α)] [obs : Observation m w] :
  obs.observe (r.recOn d y) = r.recOn (fun b => obs.observe (d b)) (fun b => obs.observe (y b)) := by
  cases r
  case yield => simp
  case done => simp

theorem Observation.forIn_list {α β} {m : Type u → Type v} {w : Type u → Type x}
  [Monad m] [∀{α}, Preorder (w α)] [obs : Observation m w]
  {xs : List α} {init : β} {f : α → β → m (ForInStep β)}
  (inv : List α → w β)
  (hpre : pure init ≤ inv xs)
  (hstep : ∀ hd tl,
      (inv (hd :: tl) >>= fun b => obs.observe (f hd b)) ≤ .yield <$> inv tl
    ∨ (inv (hd :: tl) >>= fun b => obs.observe (f hd b)) ≤ .done  <$> inv []) :
    obs.observe (forIn xs init f) ≤ inv [] := by
    open Observation MonadOrdered in
    -- Intuition: inv encapsulates the effects of looping over a prefix of xs (and gets passed the suffix)
    -- The induction hypothesis is:
    let prog suffix := inv suffix >>= fun b => obs.observe (forIn suffix b f)
    suffices hind : prog xs ≤ prog [] by
      -- This is because the predicate transformer is stronger (≤) than the invariant,
      -- and the longer the suffix passed to `prog`, the more we rely on predicate transformer.
      -- Conversely, the shorter the suffix, the more we rely on the invariant summarizing the effects of looping over a prefix.
      have : LawfulMonad w := inferInstance
      calc obs.observe (forIn xs init f)
        _ = pure init >>= fun b => obs.observe (forIn xs b f) := by simp only [pure_bind] -- only [List.forIn_nil, obs.pure_pure, bind_pure]
        -- For the after case (xs=[]), we have a lower bound because `forIn [] b` reduces to `pure b`
        _ ≤ inv xs >>= fun b => obs.observe (forIn xs b f) := bind_mono hpre (by rfl)
        -- For the initial case (full xs), we have an upper bound via hpre
        _ ≤ inv [] >>= fun b => obs.observe (forIn [] b f) := hind
        _ = inv [] := by simp
    -- Now prove hind : prog xs ≤ prog [] by induction
    clear hpre -- not needed any longer and would need to be generalized
    induction xs
    case nil => simp_all only [List.nil_append, le_refl]
    case cons hd tl h =>
      simp only [prog, List.forIn_cons, Observation.bind_bind, ←bind_assoc]
      cases hstep hd tl
      case inl hstep =>
        apply LE.le.trans _ h
        simp only [prog, List.forIn_cons, Observation.bind_bind, ←bind_assoc]
        apply LE.le.trans (MonadOrdered.bind_mono hstep (by rfl))
        simp only [bind_map_left, le_refl]
      case inr hstep =>
        simp only [prog, List.forIn_cons, List.forIn_nil, Observation.bind_bind, ←bind_assoc]
        apply LE.le.trans (MonadOrdered.bind_mono hstep (by rfl))
        simp only [bind_map_left, le_refl, prog]

theorem Observation.foldlM_list {α β} {m : Type u → Type v} {w : Type u → Type x}
  [Monad m] [LawfulMonad m] [∀{α}, Preorder (w α)] [obs : Observation m w]
  {xs : List α} {init : β} {f : β → α → m β}
  (inv : List α → w β)
  (hpre : pure init ≤ inv xs)
  (hstep : ∀ hd tl,
      (inv (hd :: tl) >>= fun b => obs.observe (f b hd)) ≤ inv tl) :
    obs.observe (xs.foldlM f init) ≤ inv [] := by
  have : xs.foldlM f init = forIn xs init (fun a b => .yield <$> f b a) := by
    simp only [List.forIn_yield_eq_foldlM, id_map']
  rw[this]
  apply Observation.forIn_list inv hpre
  intro hd tl
  left
  have : .yield <$> (inv (hd :: tl) >>= fun b => obs.observe (f b hd)) ≤ ForInStep.yield <$> inv tl := MonadOrdered.map_mono (hstep hd tl)
  simp only [map_bind] at this
  simp only [map_map, this]

theorem Observation.forIn_range {β} {m : Type u → Type v} {w : Type u → Type x}
  [Monad m] [∀{α}, Preorder (w α)] [obs : Observation m w]
  {xs : Std.Range} {init : β} {f : ℕ → β → m (ForInStep β)}
  (inv : List Nat → w β)
  (hpre : pure init ≤ inv (List.range' xs.start xs.size xs.step))
  (hstep : ∀ hd tl,
      (inv (hd :: tl) >>= fun b => obs.observe (f hd b)) ≤ .yield <$> inv tl
    ∨ (inv (hd :: tl) >>= fun b => obs.observe (f hd b)) ≤ .done <$> inv []) :
    obs.observe (forIn xs init f) ≤ inv [] := by
    rw [Std.Range.forIn_eq_forIn_range']
    exact Observation.forIn_list inv hpre hstep

theorem Observation.forIn_loop {β} {m : Type u → Type v} {w : Type u → Type x}
  [Monad m] [∀{α}, Preorder (w α)] [obs : Observation m w]
  {init : β} {f : Unit → β → m (ForInStep β)}
  (term : False)
  (inv : w β)
  (hpre : pure init ≤ inv)
  (hstep :
      (inv >>= fun b => obs.observe (f () b)) ≤ .yield <$> inv
    ∨ (inv >>= fun b => obs.observe (f () b)) ≤ .done <$> inv) :
    obs.observe (Loop.mk.forIn init f) ≤ inv := term.elim

-- TBD: Figure this out
--theorem Observation.forIn_while {β} {m : Type u → Type v} {w : Type u → Type x} {c : β → Bool}
--  [Monad m] [∀{α}, Preorder (w α)] [obs : Observation m w]
--  {init : β} {f : β → m β}
--  (term : False)
--  (inv : w β)
--  (hpre : ¬ c init → pure init ≤ inv)
--  (hstep : ∀ b,
--      (inv >>= fun b => obs.observe (f b)) ≤ inv) :
--    obs.observe (Loop.mk.forIn init (fun _ b => if c b then ForInStep.yield <$> f b else pure (ForInStep.done b))) ≤ inv := term.elim

-- the following theorem does not work as a simp lemma:
theorem Observation.forIn_range2 {β} {m : Type u → Type v} {w : Type u → Type x}
  [Monad m] [lat : ∀{α}, Preorder (w α)] [obs : Observation m w]
  {xs : Std.Range} {init : β} {f : ℕ → β → m (ForInStep β)} {wp : w β}
  (inv : List Nat → w β)
  (hpre : pure init ≤ inv (List.range' xs.start xs.size xs.step))
  (hstep : ∀ hd tl,
      (inv (hd :: tl) >>= fun b => obs.observe (f hd b)) ≤ .yield <$> inv tl
    ∨ (inv (hd :: tl) >>= fun b => obs.observe (f hd b)) ≤ .done <$> inv [])
  (hgoal : inv [] ≤ wp) :
    obs.observe (forIn xs init f) ≤ wp ↔ True :=
    iff_true_intro (le_trans (Observation.forIn_range inv hpre hstep) hgoal)

end Observation

section Triple

class MonadTriple (w : Type u → Type v) (prop : outParam (Type (u+1))) [Preorder prop] where
  wp : w α → (α → prop) → prop

instance PredTrans.instMonadTriple : MonadTriple PredTrans HProp where
  wp t := t.trans

instance StateT.instMonadTriple {w : Type u → Type v} {prop : outParam (Type (u+1))} [Preorder prop] [MonadTriple w prop] : MonadTriple (StateT σ w) (σ → prop) where
  wp t q s := MonadTriple.wp (t s) fun (a, s') => q a s'

instance ExceptT.instMonadTriple {w : Type u → Type v} {prop : outParam (Type (u+1))} [Preorder prop] [MonadTriple w prop] : MonadTriple (ExceptT ε w) prop where
  wp t q := MonadTriple.wp t.run fun e => match e with | .ok a => q a | .error ε => False

def PredTrans.Pure.Triple [Monad m] [Observation m PredTrans] (P : Prop) (x : m α) (Q : α → Prop) : Prop :=
  HProp.persistent P ≤ (Observation.observe x).trans (fun a => HProp.persistent (Q a))

example : (∀ x, p x → pure x ≤ PredTrans.persistent q) ↔ p ≤ q := by
  simp only [PredTrans.le_pure_post]
  rfl

example : PredTrans.Pure.Triple P x Q = ((fun Q => HProp.persistent P ≤ Q) ≤ Observation.observe x) := by
  rfl

example : (HProp.persistent P ≤ (PredTrans.persistent Q₁).trans (HProp.persistent ∘ Q₂)) = (∀ a, (P ∧ (Q₁ a)) ≤ (Q₂ a)) := by
  calc _
    _ = (P ≤ (∀' a, Q₁ a -⋆ Q₂ a)) := by simp[PredTrans.post]
    _ = (∀ μ, P μ → (∀' a, Q₁ a -⋆ Q₂ a) μ) := by rfl
    _ = (∀ μ, P μ → ∀ a, (Q₁ a -⋆ Q₂ a) μ) := by simp
    _ = (∀ μ, P μ → ∀ a μ', μ.Disjoint μ' → Q₁ a μ' → Q₂ a (μ ∪ μ')) := by simp
    _ = (∀ a μ μ', μ.Disjoint μ' → P μ → Q₁ a μ' → Q₂ a (μ ∪ μ')) := by sorry
    _ = (∀ a μ μ', μ.Disjoint μ' → P μ → Q₁ a μ' → Q₂ a (μ ∪ μ')) := by sorry
    _ = (∀ a μ, (P ⋆ Q₁ a) μ ≤ Q₂ a μ) := by simp[HProp.sep_conj]; sorry -- just do the subst
    _ = (∀ a, (P ⋆ Q₁ a) ≤ Q₂ a) := by rfl

example : (P ≤ (PredTrans.post Q₁).trans Q₂) = (∀ a, (P ⋆ Q₁ a) ≤ Q₂ a) := by
  calc _
    _ = (P ≤ (∀' a, Q₁ a -⋆ Q₂ a)) := by simp[PredTrans.post]
    _ = (∀ μ, P μ → (∀' a, Q₁ a -⋆ Q₂ a) μ) := by rfl
    _ = (∀ μ, P μ → ∀ a, (Q₁ a -⋆ Q₂ a) μ) := by simp
    _ = (∀ μ, P μ → ∀ a μ', μ.Disjoint μ' → Q₁ a μ' → Q₂ a (μ ∪ μ')) := by simp
    _ = (∀ a μ μ', μ.Disjoint μ' → P μ → Q₁ a μ' → Q₂ a (μ ∪ μ')) := by sorry
    _ = (∀ a μ μ', μ.Disjoint μ' → P μ → Q₁ a μ' → Q₂ a (μ ∪ μ')) := by sorry
    _ = (∀ a μ, (P ⋆ Q₁ a) μ ≤ Q₂ a μ) := by simp[HProp.sep_conj]; sorry -- just do the subst
    _ = (∀ a, (P ⋆ Q₁ a) ≤ Q₂ a) := by rfl

def PredTrans.Triple [Monad m] [Observation m PredTrans] (P : HProp) (x : m α) (Q : α → HProp) : Prop :=
  P ≤ (Observation.observe x).trans Q
notation "<<" P ">> " x " <<" Q ">>" => PredTrans.Triple P x Q
notation:lead "⦃" P "⦄ " x:lead " ⦃" Q "⦄" => PredTrans.Triple P x Q
notation:lead "⦃" P "⦄ " x:lead " ⦃" v ", " Q "⦄" => PredTrans.Triple P x (fun v => Q)

theorem weaken [Monad m] [Observation m PredTrans] {P₁ P₂ : HProp} {x : m α} {Q₁ Q₂ : α → HProp}
  (hspec : ⦃P₂⦄ x ⦃Q₂⦄) (himp₁ : P₁ ≤ P₂ := by rfl) (himp₂ : Q₂ ≤ Q₁ := by rfl) :
  ⦃ P₁ ⦄ x ⦃ Q₁ ⦄ := by
  intro μ hp
  apply (Observation.observe x).mono _ _ himp₂
  exact hspec μ (himp₁ μ hp)

theorem spec [Monad m] [Observation m PredTrans] {P₁ P₂ : HProp} {x : m α} {f : α → m β} {Q₁ : α → HProp} {Q₂ : β → HProp}
  (hspec : ⦃P₂⦄ x ⦃Q₁⦄) (himp₁ : P₁ ≤ P₂ := by simp) (himp₂ : Q₂ ≤ Q₃ := by rfl) (hgoal : ∀ a, ⦃ Q₁ a ⦄ f a ⦃ Q₂ ⦄) :
  ⦃ P₁ ⦄ (do let a ← x; f a) ⦃ Q₃ ⦄ := by
  intro μ hp
  rw[Observation.bind_bind]
  apply (do let a ← Observation.observe x; Observation.observe (f a)).mono _ _ himp₂
  apply (Observation.observe x).mono _ _ hgoal _ (hspec μ (himp₁ μ hp))

@[simp]
theorem PredTrans.Triple.persistent_sep_conj {p : Prop} {q : HProp} {x : IO α} :
  ⦃↟p ⋆ q⦄ x ⦃r⦄ ↔ p → ⦃q⦄ x ⦃r⦄ := by
  constructor
  · intro h hp μ hq; replace h := h μ; simp at h; exact h hp μ hq sorry rfl
  · intro h μ; simp; intro hp μ hq hdis hμ; subst hμ; exact h hp μ hq

@[simp]
theorem PredTrans.Triple.exists {p : α → HProp} {x : IO β} {q : β → HProp} :
  ⦃∃' a, p a⦄ x ⦃q⦄ ↔ ∀ a, ⦃p a⦄ x ⦃q⦄ := by
  constructor
  · intro h a μ hp; exact h μ (HProp.exists_exists.mpr ⟨a, hp⟩)
  · intro h μ; simp; exact (fun a => h a μ)

@[simp]
theorem PredTrans.Triple.map {p : HProp} {x : IO α} {q : β → HProp} :
  ⦃p⦄ (f <$> x) ⦃q⦄ ↔ ⦃p⦄ x ⦃fun a => q (f a)⦄ := by
  constructor
  · intro h μ hp; have h := h μ hp; simp at h; exact h
  · intro h μ hp; have h := h μ hp; simp; exact h

@[simp]
theorem HProp.single_implies {l : Loc} {x y : α} :
  ((l ↦ x) ≤ (l ↦ y)) ↔ x = y := by
  constructor
  · intro h; have h := h (Heap.single l (Sigma.mk α x)); simp at h; have h := congrArg AList.entries h; simp[Heap.single] at h; injection h
  · intro h; exact h ▸ le_refl _

end Triple

section Idd

@[ext]
structure Idd (α : Type u) where
  run : α

def Idd.pure (a : α) : Idd α := ⟨a⟩
def Idd.bind (x : Idd α) (f : α → Idd β) : Idd β := f x.run
instance : Monad Idd where
  pure := Idd.pure
  bind := Idd.bind

instance : LawfulMonad Idd where
  bind_pure_comp := by intros; constructor
  pure_bind := by intros; constructor
  bind_assoc := by intros; constructor
  bind_map := by intros; constructor
  map_const := sorry
  id_map := sorry
  pure_seq := sorry
  seqLeft_eq := sorry
  seqRight_eq := sorry

instance Idd.instObservation : Observation Idd PredTrans where
  observe := fun x p => (Pure.pure x.run).trans (fun a => )  Heap.empty
  pure_pure := by simp[Pure.pure, pure, implies_true]
  bind_bind := by simp[Bind.bind, bind, ↓pure_bind, implies_true]

theorem Idd.observe_run {p : α → Prop} {e : Idd α} :
  (Observation.observe e).trans (fun a => ↟(p a)) Heap.empty
  ↔ p e.run := by
  simp only [Observation.observe, Pure.pure, PredTrans.pure, PredTrans.persistent_elim,
    HProp.persistent_intro, and_true, forall_eq]

theorem Idd.observe_nf : Observation.observe (e : Idd α) = Pure.pure e.run := by rfl

theorem Idd.observe_post : Observation.observe (e : Idd α) ≤ PredTrans.persistent p ↔ p e.run := by
  simp only [Observation.observe, PredTrans.le_pure_post]

end Idd

section IO

@[simp]
theorem EStateM.pure_inj [inh : Inhabited σ] : pure (f := EStateM ε σ) x = pure y ↔ x = y := by
  constructor
  case mp =>
    intro h
    injection congrArg (·.run inh.default) h
  case mpr => intro h; simp[h]

@[simp]
axiom IO.pure_inj {α} {x y : α} : pure (f := IO) x = pure y ↔ x = y -- just as for EStateM, but unsafe. Yet very reasonable; part of the TCB

axiom IO.observe {α} (x : IO α) : PredTrans α
axiom IO.observe_pure {α} {x : α} : IO.observe (pure x) = PredTrans.pure x
axiom IO.observe_bind {α β} (x : IO α) (f : α → IO β) : IO.observe (x >>= f) = IO.observe x >>= fun a => IO.observe (f a)

set_option pp.universes true in
noncomputable instance IO.instObservation : Observation IO PredTrans where
  observe := IO.observe
  pure_pure := IO.observe_pure
  bind_bind x f := IO.observe_bind x f

axiom IO.subst {α β} {x : IO α} {p : α → Prop} {f g : α → IO β}
  (hk : ∀ {β} {f g : α → IO β}, (∀ a, p a → f a = g a))
  (hsub : IO.observe x ≤ PredTrans.persistent p) :
  x >>= f = x >>= g

theorem PredTrans.Triple.forIn_list {α β}
  {xs : List α} {init : β} {f : α → β → IO (ForInStep β)}
  (inv : List α → β → HProp)
  (hstep : ∀ hd tl b,
      ⦃inv (hd :: tl) b⦄ f hd b ⦃r, match r with | .yield b => inv tl b | .done b => inv [] b⦄) :
  ⦃inv xs init⦄ forIn xs init f ⦃inv []⦄ :=  sorry

theorem PredTrans.Triple.forIn_list_state {α β}
  {xs : List α} {init : β} {f : α → β → StateT σ IO (ForInStep β)}
  (inv : List α → β → σ → xProp)
  (hstep : ∀ hd tl b,
      ⦃inv (hd :: tl) b⦄ f hd b ⦃r, match r with | .yield b => inv tl b | .done b => inv [] b⦄) :
  ⦃inv xs init⦄ forIn xs init f ⦃inv []⦄ :=  sorry

theorem PredTrans.Triple.forIn_list_except {α β}
  {xs : List α} {init : β} {f : α → β → ExceptT ε IO (ForInStep β)}
  (inv : List α → β → HProp)
  (hstep : ∀ hd tl b,
      ⦃inv (hd :: tl) b⦄ f hd b ⦃r, match r with | .yield b => inv tl b | .done b => inv [] b⦄) :
  ⦃inv xs init⦄ forIn xs init f ⦃inv []⦄ :=  sorry

end IO

gen_injective_theorems% ForInStep

-- the following two lemmas are actually a bit ineffective because post_bind_pure
-- wins when a and b are representable by post. Also, often it's not a plain map
-- but rather `fun a => .yield (a + hd)`, and then we would need to exploit general
-- injectivity.
@[simp]
theorem PredTrans.ForInStep_yield_cancel {a b : PredTrans α} : ForInStep.yield <$> a ≤ ForInStep.yield <$> b ↔ a ≤ b := by
  sorry
--  constructor
--  case mp =>
--    intro h p
--    replace h := h (fun s => ∃ a, s = .yield a ∧ p a)
--    simp[←bind_pure_comp, Pure.pure, pure, Bind.bind, bind] at h
--    exact h
--  case mpr =>
--    intro h p μ
--    simp[←bind_pure_comp, Pure.pure, pure, Bind.bind, bind]
--    exact h (fun a => p (.yield a)) μ

@[simp]
theorem PredTrans.ForInStep_done_cancel {a b : PredTrans α} : ForInStep.done <$> a ≤ ForInStep.done <$> b ↔ a ≤ b := by
  sorry
--   constructor
--   case mp =>
--     intro h p
--     replace h := h (fun s => ∃ a, s = .done a ∧ p a)
--     simp[←bind_pure_comp, Pure.pure, pure, Bind.bind, bind] at h
--     exact h
--   case mpr =>
--     intro h p
--     simp[←bind_pure_comp, Pure.pure, pure, Bind.bind, bind]
--     exact h (fun a => p (.done a))

@[simp]
theorem Observation.ite {x y : m α} {c : Prop} [Decidable c] [Monad m] [∀{α}, Preorder (w α)] [Observation m w] :
  Observation.observe (if c then x else y) = if c then Observation.observe x else Observation.observe y := by
    split <;> simp

@[simp]
theorem Observation.dite {c : Prop} [Decidable c] {t : c → m α} {e : ¬c → m α} [Monad m] [∀{α}, Preorder (w α)] [Observation m w] :
  Observation.observe (dite c t e) = dite c (fun h => Observation.observe (t h)) (fun h => Observation.observe (e h)) := by
    split <;> simp

@[simp]
theorem PredTrans.if_then_else {x y : m α} {b : Bool} [Monad m] [∀{α}, Preorder (w α)] [Observation m w] :
  Observation.observe (if b then x else y) = if b then Observation.observe x else Observation.observe y := by
    cases b <;> simp

theorem use_spec_bind {w : Type u → Type x} {f : α → w β} {x y : w α} {goal : w β} [∀ {α}, Preorder (w α)] [MonadOrdered w]
  (hrw : x ≤ y) (hgoal : y >>= f ≤ goal) : x >>= f ≤ goal :=
  le_trans (MonadOrdered.bind_mono hrw (by rfl)) hgoal

theorem use_spec_map {w : Type u → Type x} {f : α → β} {x y : w α} {goal : w β} [∀ {α}, Preorder (w α)] [MonadOrdered w]
  (hrw : x ≤ y) (hgoal : f <$> y ≤ goal) : f <$> x ≤ goal :=
  le_trans (MonadOrdered.map_mono hrw) hgoal

--theorem use_spec_seq {w : Type u → Type x} {f : w (α → β)} {x y : w α} {goal : w β} [∀ {α}, Preorder (w α)] [MonadOrdered w]
--  (hrw : x ≤ y) (hgoal : f <*> y ≤ goal) : f <*> x ≤ goal :=
--  le_trans (MonadOrdered.seq_mono (by rfl) hrw) hgoal

macro (name := vc_spec_Idd) "vc_spec_Idd " post:term : tactic =>
  `(tactic|(apply (Idd.observe_post (p := $post)).mp; simp))

theorem test_3 : Observation.observe (do let mut x := 0; for i in [1:5] do { x := x + i }; pure (f := Idd) (); return x) ≤ PredTrans.persistent (· < 30) := by
  simp
  apply le_trans (Observation.forIn_list ?inv ?hpre ?hstep) ?hgoal
  case inv => exact fun xs => PredTrans.persistent fun r => (∀ x, x ∈ xs → x ≤ 5) ∧ r + xs.length * 5 ≤ 25
  case hpre => simp_arith
  case hstep => simp_arith; intro hd tl; left; intro r x h h1 h2; subst h; simp_all; omega
  case hgoal => simp_arith

theorem test_3_2 : Observation.observe (do let mut x := 0; for i in [1:5] do { x := x + i }; pure (f := Idd) (); return x) ≤ pure 10 := by
  simp
  apply le_trans (Observation.forIn_list ?inv ?hpre ?hstep) ?hgoal
  case inv => exact fun xs => PredTrans.persistent fun r => r + xs.sum = 10
  case hpre => simp_arith
  -- sigh. the following could be much better! TODO
  case hstep => simp_arith; intro hd tl; left; intro r x h h1; subst h; simp_all
  case hgoal => simp

-- TBD: Figure out while loops
theorem test_4 : Observation.observe (do let mut x := 0; let mut i := 0; while i < 4 do { x := x + i; i := i + 1 }; pure (f := Idd) (); return x) ≤ pure 6 := by
  simp
  apply use_spec_map (Observation.forIn_loop ?term ?inv ?hpre ?hstep) ?hgoal
  case term => sorry
  case inv => exact PredTrans.persistent fun | ⟨i, x⟩ => x + (List.range' i (4-i) 1).sum = 6
  case hpre => simp_arith
  case hstep => sorry
  case hgoal => simp; sorry -- later: conv => lhs; arg 1; intro x; tactic =>

theorem test_1 : Observation.observe (do let mut id := 5; id := 3; pure (f := Idd) id) ≤ pure 3 := by
  simp

theorem test_2 : Observation.observe (do let mut x := 5; if x > 1 then { x := 1 } else { x := x }; pure (f:=Idd) x) ≤ pure 1 := by
  simp

theorem test_2_2 : Observation.observe (do let mut id := 5; id := 3; pure (f := Idd) id) ≤ PredTrans.persistent (· < 20) := by
  simp

section UserStory1

def FinSimpleGraph (n : ℕ) := SimpleGraph (Fin n)
open SimpleGraph
open Finset
open Classical

open Std

def FinSimpleGraph.IsSpannerOf {n:ℕ } (H G : FinSimpleGraph n)  (t:ℕ)  : Prop := H.IsSubgraph G ∧ H.Connected ∧  ∀ u v : Fin n, H.dist u v ≤ t * G.dist u v

noncomputable def FinSimpleGraph.numEdges {n : ℕ}(G : FinSimpleGraph n) : ℕ := #G.edgeFinset

def AddEdge {n :ℕ}(M : Fin n → Fin n → Prop) ( e : Sym2 (Fin n) ): Fin n → Fin n → Prop := fun (i j : Fin n) ↦ M i j ∨ (e = s(i,j))

noncomputable def dist {n :ℕ}(M : Fin n → Fin n → Prop) (e : Sym2 (Fin n)): ℕ := (SimpleGraph.fromRel M).dist (Quot.out e).1 (Quot.out e).2

noncomputable def greedySpanner {n:ℕ }(G : FinSimpleGraph n) (t :ℕ ): FinSimpleGraph n := Idd.run do
  let mut f_H : Fin n → Fin n → Prop := fun (_ _) ↦ false
  for e in G.edgeFinset.toList do
    if (2*t -1) < dist f_H e then f_H := AddEdge f_H e
  return SimpleGraph.fromRel f_H

@[simp]
theorem ite_extrude_yield {c : Prop} [Decidable c] {x y : α} :
  (if c then pure (.yield x) else pure (.yield y)) = ForInStep.yield <$> if c then pure x else pure (f := Idd) y := by
  split <;> simp

lemma correctnessOfGreedySpanner {n:ℕ }(G : FinSimpleGraph n)(t :ℕ ) (u v : Fin n) :
  (greedySpanner G t).dist u v ≤ 2*t-1 := by
    vc_spec_Idd (fun r => SimpleGraph.dist r u v ≤ 2*t-1)
    apply le_trans (Observation.foldlM_list ?inv ?hpre ?hstep) ?hgoal
    case inv => exact fun xs => PredTrans.persistent fun f_H => ∀ i j, f_H i j → 2*t-1 < dist f_H s(i,j)
    case hpre => simp
    case hstep =>
      intro e es
      apply PredTrans.bind_persistent; intro f_H hinv
      if h : 2*t-1 < dist f_H e
      then
        simp[h]
        show ∀ (i j : Fin n), AddEdge f_H e i j → 2 * t - 1 < _root_.dist (AddEdge f_H e) s(i, j)
        -- domain-specific, pure proof
        sorry
      else
        simp[h]
        show  ∀ (i j : Fin n), f_H i j → 2 * t - 1 < _root_.dist f_H s(i, j)
        -- domain-specific, pure proof
        sorry
    case hgoal =>
      simp
      show ∀ (x : Fin n → Fin n → Prop),
        (∀ (i j : Fin n), x i j → 2 * t - 1 < _root_.dist x s(i, j)) →
        (fromRel x).dist u v ≤ 2 * t - 1
      -- domain-specific, pure proof
      sorry

end UserStory1

section fib

def fib_impl (n : Nat) := Idd.run do
  if n = 0 then return 0
  let mut a := 0
  let mut b := 1
  for _ in [1:n] do
    let a' := a
    a := b
    b := a' + b
  return b

def fib_spec : Nat → Nat
| 0 => 0
| 1 => 1
| n+2 => fib_spec n + fib_spec (n+1)

theorem fib_spec_rec (h : n > 1) : fib_spec n = fib_spec (n-2) + fib_spec (n-1) := by
  rw (occs := .pos [1]) [fib_spec.eq_def]
  split
  repeat omega
  simp

theorem fib_correct {n} : fib_impl n = fib_spec n := by
  vc_spec_Idd (· = fib_spec n)
  if h : n = 0 then simp[h,fib_spec] else ?_
  simp [h,fib_spec]
  apply use_spec_map (Observation.forIn_list ?inv ?hpre ?hstep)
  case inv => exact fun xs => PredTrans.persistent fun
    | ⟨a, b⟩ => let i := n - xs.length; xs.length < n ∧ a = fib_spec (i-1) ∧ b = fib_spec i
  case hpre => simp_arith [Nat.succ_le_of_lt, Nat.zero_lt_of_ne_zero h, Nat.sub_sub_eq_min]
  case hstep =>
    simp_arith
    intro tl
    left
    conv => rfl
    intro r ⟨a, b⟩ hr h1 h2 h3
    subst hr
    replace h1 : tl.length + 1 < n := Nat.add_one_le_iff.mpr h1
    simp_arith[Nat.succ_le_of_lt, Nat.zero_lt_of_ne_zero h, Nat.sub_sub_eq_min, Nat.sub_sub, Nat.lt_of_succ_lt] at *
    simp[Nat.lt_of_succ_lt h1,h2,h3]
    refine (fib_spec_rec ?_).symm
    simp_arith[Nat.le_sub_of_add_le' h1]
  simp_arith
  intro y ⟨a, b⟩ h
  subst (h Heap.empty)
  simp

end fib

section KimsBabySteps

/-- Add `n` random even numbers to `k`. -/
def addRandomEvens (n : Nat) (k : Nat) : IO Nat := do
  let mut r := k
  for _ in List.range n do
    r := r + 2 * (← IO.rand 0 37)
  pure r

def program (n : Nat) (k : Nat) : IO Nat := do
  let r₁ ← addRandomEvens n k
  let r₂ ← addRandomEvens n k
  return r₁ + r₂

axiom IO.rand_spec {n : Nat} : Observation.observe (IO.rand 0 n : IO Nat) ≤ PredTrans.persistent (· < n)

/-- The result has the same parity as the input. -/
theorem addRandomEvens_spec (n k) : Observation.observe (addRandomEvens n k) ≤ PredTrans.persistent (fun r => r % 2 = k % 2) := by
  simp only [addRandomEvens, bind_pure_comp, map_pure, List.forIn_yield_eq_foldlM, bind_pure]
  apply le_trans (Observation.foldlM_list ?inv ?hpre ?hstep) ?hgoal
  case inv => exact fun xs => PredTrans.persistent fun r => r % 2 = k % 2
  case hpre => simp
  case hstep =>
    intro hd tl
    -- (do let b ← PredTrans.post fun r => r % 2 = k % 2
    --     Observation.observe ((fun c => b + 2 * c) <$> liftM (IO.rand 0 37)))
    -- ≤ PredTrans.post fun r => r % 2 = k % 2
    apply PredTrans.bind_persistent -- accept the spec `PredTrans.post fun r => r % 2 = k % 2` for b
    intro b hb
    -- b : Nat
    -- hb : b % 2 = k % 2
    -- Observation.observe ((fun c => b + 2 * c) <$> liftM (IO.rand 0 37))
    -- ≤ PredTrans.post fun r => r % 2 = k % 2
    simp -- only [Observation.map_map]
    -- b : Nat
    -- hb : b % 2 = k % 2
    -- Observation.observe (liftM (IO.rand 0 37))
    -- ≤ PredTrans.post fun a => b % 2 = k % 2
    apply le_trans IO.rand_spec -- apply the spec for IO.rand... not that it matters now that `a` does not occur in the post cond
    -- b : Nat
    -- hb : b % 2 = k % 2
    -- PredTrans.post (· < 37)
    -- ≤ PredTrans.post fun a => b % 2 = k % 2
    simp -- only [PredTrans.post_bind_pure, PredTrans.post_mono, forall_exists_index, and_imp]
    -- b : Nat
    -- hb : b % 2 = k % 2
    -- ∀ x < 37, b % 2 = k % 2
    omega
  simp

/-- Since we're adding even numbers to our number twice, and summing,
the entire result is even. -/
theorem program_spec (n k) : Observation.observe (program n k) ≤ PredTrans.persistent (fun r => r % 2 = 0) := by
  -- unfold program
  simp[program] -- only [program, bind_pure_comp, Observation.bind_bind, Observation.map_map]
  -- apply the spec for addRandomEvens
  apply use_spec_bind (addRandomEvens_spec n k)
  apply PredTrans.bind_persistent; intro r₁ h₁ -- accept the spec; move focus/lens to next instruction and bring in scope the post condition
  apply use_spec_map (addRandomEvens_spec n k)
  simp
  omega

theorem addRandomEvens_spec_old (n k) : SatisfiesM (fun r => r % 2 = k % 2) (addRandomEvens n k) := by
  simp [addRandomEvens]
  apply List.satisfiesM_foldlM
  · rfl
  · intros b w a m
    apply SatisfiesM.bind_pre
    simp_all [SatisfiesM_EStateM_eq, EStateM.run]

/--
Add `n` random even numbers to `k`,
returning the result and a proof it has the same parity as `k`.
-/
def addRandomEvens' (n : Nat) (k : Nat) : IO { r : Nat // r % 2 = k % 2 } := do
  satisfying (addRandomEvens_spec_old n k)

/-- Since we're adding even numbers to our number twice, and summing,
the entire result is even. -/
theorem program_spec_old (n k) : SatisfiesM (fun r => r % 2 = 0) (program n k) := by
  -- unfold program
  rw [program]
  -- apply the spec for addRandomEvens
  obtain ⟨r₁, h₁⟩ := addRandomEvens_spec_old n k
  simp [← h₁]
  -- now deal with `SatisfiesM`, fairly mechanically
  apply SatisfiesM.bind_pre
  apply SatisfiesM.of_true
  rintro ⟨x, hx⟩
  apply SatisfiesM.map_pre
  apply SatisfiesM.of_true
  rintro ⟨y, hx⟩
  -- finally, an honest goal:
  dsimp
  omega

end KimsBabySteps

section Counter

def Counter := IO.Ref Nat

def Counter.new : IO Counter := IO.mkRef 0

def Counter.incr (c : Counter) : IO Unit := (c : IO.Ref Nat).modify (· + 1)

def Counter.get (c : Counter) : IO Nat := ST.Prim.Ref.get c

def Counter.free (c : Counter) : IO Unit := pure ()

def test : IO Nat := do
  let c ← Counter.new
  c.incr
  c.incr
  let n ← c.get
  c.free
  pure n

axiom IO.refAt {α} : Loc → IO.Ref α

axiom IO.mkRef_spec {α : Type} {x : α} :
  ⦃ emp ⦄ (IO.mkRef x : IO (IO.Ref α)) ⦃fun (r : IO.Ref α) => ∃' l, ↟(r = IO.refAt l) ⋆ l ↦ x⦄

axiom IO.modify_spec {α : Type} {l : Loc} {x : α} {f : α → α} :
  ⦃l ↦ x⦄ ((IO.refAt l).modify f : IO Unit) ⦃fun _ => l ↦ f x⦄

axiom IO.get_spec {α : Type} {l : Loc} {x : α} :
  ⦃l ↦ x⦄ (ST.Prim.Ref.get (IO.refAt l) : IO α) ⦃fun r => ↟(r = x) ⋆ l ↦ x⦄

theorem Counter.new_spec : ⦃ emp ⦄ Counter.new ⦃fun (c : Counter) => ∃' l, ↟(c = IO.refAt l) ⋆ l ↦ 0⦄ :=
  IO.mkRef_spec

theorem Counter.incr_spec : ⦃l ↦ n⦄ Counter.incr (IO.refAt l) ⦃fun _ => l ↦ n+1⦄ :=
  IO.modify_spec

theorem Counter.get_spec : ⦃l ↦ n⦄ Counter.get (IO.refAt l) ⦃fun r => ↟(r = n) ⋆ l ↦ n⦄ :=
  IO.get_spec

axiom Counter.free_spec {α : Type} {l : Loc} {x : α} :
  ⦃l ↦ x⦄ (Counter.free (IO.refAt l) : IO Unit) ⦃fun _ => emp⦄

theorem test_spec : ⦃ emp ⦄ test ⦃fun r => ↟(r = 2)⦄ := by
  apply spec Counter.new_spec (by simp); intro c _; simp; intro l hp; subst hp
  apply spec (Counter.incr_spec (n := 0)) (by simp); simp
  apply spec (Counter.incr_spec (n := 1)) (by simp); simp
  apply spec (Counter.get_spec (n := 2)) (by simp); simp
  apply Counter.free_spec
end Counter

section NITest

def NI.embed (S : Set (σ × Set (α × σ))) : StateT σ PredTrans α := fun s =>
  ⟨fun Q => (s, Q) ∈ S, by intro p q hpq; simp; sorry⟩ -- can't show monotonicity. unsurprisingly?

def noninterference (x : StateT (Nat × Nat) Idd α) := -- fst is low, snd is high
  -- nope, this does not work out. the post condition has no means to vary σ
  StateT.instObservationState.observe x ≤ NI.embed { (σ, Q) | ∀ α₁ α₂ σ₂ σ₂', (α₁, σ₂) ∈ Q → (α₂, σ₂') ∈ Q → α₁ = α₂ }

end NITest
