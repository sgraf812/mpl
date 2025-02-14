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

def PredTrans.mono {α} (t : (α → Prop) → Prop) : Prop :=
  ∀ p q, p ≤ q → t p → t q

def PredTrans (α : Type u) : Type u :=
  { t : (α → Prop) → Prop // PredTrans.mono t }

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
def PredTrans.post (post : α → Prop) : PredTrans α :=
  ⟨fun p => post ≤ p, fun _ _ hpq hpostp => le_trans hpostp hpq⟩

def PredTrans.pre (pre : Prop) : PredTrans α :=
  ⟨fun _ => pre, fun _ _ _ hpostp => hpostp⟩

-- In case we have a trace property, the following function is injective and right-inverse to PredTrans.post, i.e.,
--   post t.get = t.
-- In fact, this is perhaps the characteristic property of deterministic program semantics.
-- def PredTrans.get {α} (t : PredTrans α) : (α → Prop) := fun x => ∀ p, t.val p → p x

@[ext]
theorem PredTrans.ext {α} {x y : PredTrans α} (h : ∀ p, x.val p = y.val p) : x = y := by
  simp[PredTrans]; ext p; simp[h]

@[reducible]
def PredTrans.le {α} (a b : PredTrans α) : Prop :=
  ∀ p, b.val p ≤ a.val p
def PredTrans.bot {α} : PredTrans α :=
  PredTrans.post (fun _ => False)
def PredTrans.top {α} : PredTrans α :=
  PredTrans.post (fun _ => True)
def PredTrans.inf {α} (a b : PredTrans α) : PredTrans α :=
  ⟨fun x => a.val x ⊓ b.val x, fun _ _ h => And.imp (a.property _ _ h) (b.property _ _ h)⟩
def PredTrans.sup {α} (a b : PredTrans α) : PredTrans α :=
  ⟨fun x => a.val x ⊔ b.val x, fun _ _ h => Or.imp (a.property _ _ h) (b.property _ _ h)⟩
def PredTrans.sInf {α} (s : Set (PredTrans α)) : PredTrans α :=
  ⟨fun p => ∀ w ∈ s, w.val p, fun _ _ hpq h w hws => w.property _ _ hpq (h w hws)⟩
def PredTrans.sSup {α} (s : Set (PredTrans α)) : PredTrans α :=
  ⟨fun p => ∃ w ∈ s, w.val p, fun _ _ hpq => fun | ⟨w, hws, h⟩ => ⟨w, hws, w.property _ _ hpq h⟩⟩

instance PredTrans.instLE : LE (PredTrans α) := ⟨PredTrans.le⟩

instance PredTrans.instPreorder : Preorder (PredTrans α) where
  __ := PredTrans.instLE
  le_refl := fun _ _ hp => hp
  le_trans := fun a b c hab hbc p => (hbc p).trans (hab p)
instance PredTrans.instPartialOrder : PartialOrder (PredTrans α) where
  __ := PredTrans.instPreorder
  le_antisymm := fun _ _ hab hba => PredTrans.ext fun p => (hba p).antisymm (hab p)
instance PredTrans.instSemilatticeSup : SemilatticeSup (PredTrans α) where
  __ := PredTrans.instPartialOrder
  sup := PredTrans.sup
  le_sup_left := sorry
  le_sup_right := sorry
  sup_le := sorry
instance PredTrans.instSemilatticeInf : SemilatticeInf (PredTrans α) where
  __ := PredTrans.instPartialOrder
  inf := PredTrans.inf
  inf_le_left := sorry
  inf_le_right := sorry
  le_inf := sorry
instance PredTrans.instLattice : Lattice (PredTrans α) where
  __ := PredTrans.instSemilatticeSup
  __ := PredTrans.instSemilatticeInf
instance PredTrans.instCompleteLattice : CompleteLattice (PredTrans α) where
  __ := inferInstanceAs (Lattice (PredTrans α))
  top := PredTrans.top
  bot := PredTrans.bot
  sInf := PredTrans.sInf
  sSup := PredTrans.sSup
  le_top := sorry
  bot_le := sorry
  le_sInf := sorry
  le_sSup := sorry
  sInf_le := sorry
  sSup_le := sorry

def PredTrans.pure {α} (x : α) : PredTrans α :=
  ⟨fun p => p x, fun _ _ hpq => hpq x⟩
def PredTrans.bind {α β} (x : PredTrans α) (f : α → PredTrans β) : PredTrans β :=
  ⟨fun p => x.val (fun a => (f a).val p), fun _ _ hpq => x.property _ _ (fun a => (f a).property _ _ hpq)⟩

instance PredTrans.instMonad : Monad PredTrans where
  pure := PredTrans.pure
  bind := PredTrans.bind
instance PredTrans.instLawfulMonad : LawfulMonad PredTrans where
  bind_pure_comp := by intros; ext p; simp [Bind.bind, PredTrans.bind, Pure.pure, PredTrans.pure, Functor.map, Function.comp_apply]
  pure_bind := by intros; ext p; simp [Bind.bind, PredTrans.bind, Pure.pure, PredTrans.pure]
  bind_assoc := by intros; ext p; simp [Bind.bind, PredTrans.bind]
  bind_map := by intros; ext p; simp [Bind.bind, PredTrans.bind, Functor.map, Function.comp_apply, PredTrans.pure, Seq.seq]
  map_pure := by intros; ext p; simp [Bind.bind, PredTrans.bind, Pure.pure, PredTrans.pure, Functor.map, Function.comp_apply]
  map_const := sorry
  id_map := sorry
  pure_seq := sorry
  seqLeft_eq := sorry
  seqRight_eq := sorry

@[simp]
theorem PredTrans.pure_of_post {α} {x : α} : PredTrans.post (· = x) = Pure.pure x := by
  ext p
  exact Iff.intro (fun h => h x (by rfl)) (fun hp y hxy => hxy ▸ hp)

@[simp]
theorem PredTrans.post_mono : PredTrans.post p ≤ PredTrans.post q ↔ (∀ x, p x → q x) := by
  constructor
  case mp =>
    intro hqp
    simp only [post, le_Prop_eq] at hqp
    replace hqp := hqp q
    simp at hqp
    exact hqp
  case mpr =>
    intro hpq
    intro x
    simp only [post, le_Prop_eq]
    intro hpx
    exact le_trans hpq hpx

@[simp]
theorem PredTrans.pure_post_mono {α} {x : α} {p : α → Prop} : PredTrans.post p ≤ Pure.pure x ↔ ∀ y, p y → y = x := by
  simp only [← pure_of_post, post_mono]

-- for general PredTrans, it seems we cannot prove the equivalence
theorem PredTrans.post_elim {w : PredTrans α} : w ≤ PredTrans.post p → w.val p :=
  fun h => h p (le_refl p)

@[simp]
theorem PredTrans.le_pure_post {α} {x : α} {p : α → Prop} : Pure.pure x ≤ PredTrans.post p ↔ p x := by
  simp only [← PredTrans.pure_of_post, post_mono, forall_eq]

-- Just for future reference
example : PredTrans.post p ≤ Pure.pure x → p ≤ (· = x) := by
  simp[←PredTrans.pure_of_post]
  intros h
  intro y
  exact h y

@[simp]
theorem PredTrans.map_post {f : α → β} {t : PredTrans α} : (f <$> t).val p = t.val (fun a => p (f a)) := by
  simp only [Functor.map, bind, Function.comp_apply, pure]

@[simp]
theorem PredTrans.le_map_post {f : α → β} : f <$> t ≤ PredTrans.post p ↔ t ≤ PredTrans.post (fun a => p (f a)) :=
  ⟨fun h _ hq => t.property _ _ hq (PredTrans.map_post ▸ h p (le_refl _)),
   fun h _ hq => t.property _ _ (fun a => hq (f a)) (post_elim h)⟩

@[simp]
theorem PredTrans.post_bind_pure {f : α → β} : f <$> PredTrans.post p = PredTrans.post (fun b => ∃ a, f a = b ∧ p a) := by
  ext q
  simp only [Bind.bind, bind, post, pure]
  constructor
  case mpr =>
    intro h a hp
    exact h (f a) ⟨a, rfl, hp⟩
  case mp =>
    intro h b ⟨a, hfa, hp⟩
    exact hfa ▸ h a hp

theorem PredTrans.bind_post {f : α → PredTrans β} {goal : PredTrans β}
  (hgoal : ∀ a, p a → f a ≤ goal) : PredTrans.post p >>= f ≤ goal :=
  fun q hq a hp => hgoal a hp q hq

end PredTrans

section HPredTrans

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

@[simp]
theorem Heap.Disjoint_empty_left : Disjoint empty μ := sorry

@[simp]
theorem Heap.Disjoint_empty_right : Disjoint μ empty := sorry

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

protected def HProp.True : HProp :=
  ∃' (h : HProp), h

instance : Inhabited HProp where
  default := HProp.True

def HProp.sep_imp (p q : HProp) : HProp :=
  ∃' (h : HProp), h ⋆ ↟(p ⋆ h ≤ q)

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
theorem HProp.True_intro : HProp.True μ ↔ True := by
  simp[HProp.True]
  use (fun _ => True)

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

-- this is too brutal
-- @[simp]
theorem HProp.sep_conj_intro : (p ⋆ q) μ ↔ ∃ μ₁ μ₂, p μ₁ ∧ q μ₂ ∧ Heap.Disjoint μ₁ μ₂ ∧ μ = μ₁ ∪ μ₂ := by
  constructor
  · sorry
  · sorry

@[simp]
theorem HProp.sep_conj_frame_left : (p ⋆ h) ≤ (q ⋆ h) ↔ p ≤ q := by
  constructor
  · sorry
  · sorry

@[simp]
theorem HProp.sep_conj_frame_right : (h ⋆ p) ≤ (h ⋆ q) ↔ p ≤ q := by
  constructor
  · sorry
  · sorry

@[simp]
theorem HProp.sep_conj_empty : (emp ⋆ h) = h := by
  sorry

@[simp]
lemma HProp.forall_forall : (HProp.forall p) μ ↔ ∀ x, p x μ := sorry

@[simp]
lemma HProp.sep_conj_forall : ((HProp.forall p) ⋆ q) = HProp.forall (fun a => p a ⋆ q) := sorry

@[simp]
lemma HProp.sep_imp_intro : (HProp.sep_imp p q) μ ↔ ∀ μ', Heap.Disjoint μ μ' → p μ' → q (μ ∪ μ') := sorry

theorem HProp.sep_imp_conj : ((p -⋆ q) ⋆ h) μ → (p -⋆ (q ⋆ h)) μ := by
  intro hp
  simp_all[HProp.sep_conj_intro]
  obtain ⟨μ₁, hpq, μ₂, hh, hdis₁₂, hunion₁₂⟩ := hp
  intro μ' hdis hp
  have : μ₁.Disjoint μ' := sorry -- follows from hdis : μ.Disjoint μ' and hunion₁₂ : μ = μ₁ ∪ μ₂
  have hq := hpq μ' this hp
  use μ₁ ∪ μ', hq, μ₂, hh
  have : (μ₁ ∪ μ').Disjoint μ₂ := sorry -- follows from hdis : hunion₁₂ ▸ (μ₁ ∪ μ₂).Disjoint μ' and hdis₁₂ : μ₁.Disjoint μ₂
  use this, sorry -- by simp[hunion₁₂] and commutativity of ∪

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
  simp only [persistent, sep_conj_exists, sep_conj_empty, exists_exists, exists_prop]

def HPredTrans.Pre (α : Type u) : Type (u + 1) :=
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
def HPredTrans.Pre.ext {a b : HPredTrans.Pre α} : (∀ p, a p = b p) → a = b := by
  simp[HPredTrans.Pre]
  intro h
  ext p : 1
  exact h p

def HPredTrans.Mono (t : HPredTrans.Pre α) : Prop :=
  ∀ p q, p ≤ q → t p ≤ t q

def HPredTrans.Frame (t : HPredTrans.Pre α) : Prop :=
  ∀ p frame, t p ⋆ frame ≤ t (fun a => p a ⋆ frame)

structure HPredTrans (α : Type u) : Type (u + 1)where
  trans : HPredTrans.Pre α
  mono : HPredTrans.Mono trans
  frame : HPredTrans.Frame trans

@[ext]
def HPredTrans.ext {a b : HPredTrans α} : (∀ p, a.trans p = b.trans p) → a = b := by
  sorry  -- recover from history

def HPredTrans.post (post : α → HProp) : HPredTrans α :=
  { trans := fun p => ∀' a, post a -⋆ p a -- sep_imp on post conditions
    mono := by
      intro _ _ hpq μ hp
      simp_all
      intro x μ' hdis hpost
      exact hpq x (μ ∪ μ') (hp x μ' hdis hpost)
    frame := by
      intro p h μ hp
      simp at hp
      intro a
      exact HProp.sep_imp_conj (hp a)
  }

-- I'll leave these for educational purposes
def HPredTrans.post_attempt_1 (post : α → HProp) : HPredTrans α :=
  { trans := fun p μ => ∀ a, post a μ ≤ p a μ
    mono := by
      intro _ _ hpq μ hp a hpost
      exact hpq a μ (hp a hpost)
    frame := by
      intro μ₁ μ₂ p _hdis hp a hpost
      simp
      use μ₁
      simp_all only [le_Prop_eq, and_self, and_true]
      apply hp a
      show post a μ₁
      sorry -- but we only have post a (μ₁ ∪ μ₂)
  }

def HPredTrans.post_attempt_2 (post : α → HProp) : HPredTrans α :=
  { trans := fun p => ↟(∀ a h, (post a ⋆ h) ≤ (p a ⋆ h))
    mono := by
      intro _ _ hpq μ hp
      simp_all
      intro a μ hpost
      exact hpq a μ (hp.1 a μ hpost)
    frame := by
      intro μ₁ μ₂ p _hdis hp
      simp_all
      sorry -- need to show μ₂ = Heap.empty but can't
  }

def HPredTrans.post_attempt_3 (post : α → HProp) : HPredTrans α :=
  { trans := fun p μ => (∀ a h, (post a ⋆ h) ≤ (p a ⋆ h))
    mono := by
      intro _ _ hpq μ hp
      simp_all
      intro a μ hpost
      exact hpq a μ (hp a μ hpost)
    frame := by
      intro μ₁ μ₂ p _hdis hp
      simp_all
      sorry -- need to show (post a ≤ p a) → (post a ≤ p a ⋆ fun x => x = μ₂) but can't
  }

def HPredTrans.post_attempt_4 (post : α → HProp) : HPredTrans α :=
  { trans := fun p μ => (∀ a h, (post a ⋆ h) μ ≤ (p a ⋆ h) μ)
    mono := by
      intro _ _ hpq μ hp
      simp_all
      intro a h hpost
      have := hp a h hpost
      exact HProp.sep_conj_frame_left.mpr (hpq a) μ this
    frame := by
      intro μ₁ μ₂ p _hdis hp a h hpost
      simp_all
      sorry -- need to show ((post a ⋆ h) (μ₁ ∪ μ₂)) → ((p a ⋆ fun x => x = μ₂) ⋆ h) (μ₁ ∪ μ₂) but can't
  }

def HPredTrans.post_attempt_5 (post : α → HProp) : HPredTrans α :=
  { trans := fun p μ => (∀ a h μ₂ (_ : Heap.Disjoint μ μ₂), (post a ⋆ h) ≤ p a)
    mono := by
      intro _ _ hpq μ hp
      simp_all
      intro a h μ₂ hdis hpost
      have := hp a h μ₂ hdis hpost
      exact HProp.sep_conj_frame_left.mpr (hpq a) _ this
    frame := by
      intro μ₁ μ₂ p _hdis hp a h μ hdis hpost
      simp_all
      sorry -- need to show (post a (μ₁ ∪ μ₂)) → (post a μ₁), but can't
  }

def HPredTrans.post_attempt_6 (post : α → HProp) : HPredTrans α :=
  { trans := fun p μ => (∃ h, h μ ∧ ∀ a, (post a ⋆ h) ≤ p a)
    mono := by
      intro _ _ hpq μ hp
      sorry --doable
    frame := by
      intro μ₁ μ₂ p _hdis hp
      simp_all
      obtain ⟨h, hh, hpost⟩ := hp
      use h ⋆ fun x => x = μ₂
      constructor
      · simp[HProp.sep_conj_intro]
        use μ₁
      · intro a
        sorry
        -- apply HProp.sep_conj_frame_left.mpr (hpost a) -- need to reassociate ⋆ here, otherwise done
  }

def HPredTrans.persistent (post : α → Prop) : HPredTrans α :=
  HPredTrans.post (fun a => ↟(post a))

@[simp]
theorem HPredTrans.persistent_elim : (HPredTrans.persistent p).trans q μ ↔ (∀ a, p a → q a μ) := by
  simp_all[HPredTrans.persistent, HPredTrans.post]
  constructor
  · intro h a hp
    have := h a Heap.empty sorry hp rfl
    simp[this]
  · intro hpq a _ _ hp _
    exact hpq a hp

@[simp]
theorem PredTrans.post_le_post_post : (PredTrans.post p).val q ↔ PredTrans.post p ≤ PredTrans.post q := by
  simp[PredTrans.post]
  constructor
  · intro hpq r hqr
    exact hpq.trans hqr
  · intro h a hp
    have := h q
    simp at this
    exact this a hp

theorem HPredTrans.PredTrans_persistent_post :
  ((HPredTrans.persistent p).trans (fun a => HProp.persistent (q a)) Heap.empty)
  ↔ (PredTrans.post p).val q := by
  simp[HPredTrans.persistent_elim]

def HPredTrans.le (a b : HPredTrans α) :=
  ∀ p, b.trans p ≤ a.trans p

instance HPredTrans.instLE : LE (HPredTrans α) where
  le := HPredTrans.le

instance HPredTrans.instPreorder : Preorder (HPredTrans α) where
  le_refl a := by
    intro p
    apply le_refl
  le_trans a b c hab hbc := by
    intro p
    apply le_trans (hbc p) (hab p)

instance HPredTrans.instPartialOrder : PartialOrder (HPredTrans α) where
  le_antisymm a b hab hba := by
    ext p : 1
    apply le_antisymm (hba p) (hab p)

theorem HPredTrans.sep_conj_stuff {t : HPredTrans α} : (t.trans p ⋆ (· = μ₂)) ≤ t.trans (fun a => p a ⋆ (· = μ₂)) := by
  intro μ
  simp[HProp.sep_conj_intro]
  intro μ₁ hp hdis hunion
  apply hunion ▸ t.frame μ₁ μ₂ _ hdis hp

def HPredTrans.pure (a : α) : HPredTrans α :=
  HPredTrans.persistent (· = a)

def HPredTrans.bind {α β} (x : HPredTrans α) (f : α → HPredTrans β) : HPredTrans β :=
  { trans := fun p => x.trans (fun a => (f a).trans p),
    mono := fun _ _ hpq => x.mono _ _ (fun a => (f a).mono _ _ hpq),
    frame := by
      intro μ₁ μ₂ p _hdis hp
      have := x.frame μ₁ μ₂ _ _hdis hp
      apply x.mono (fun a => (f a).trans p ⋆ fun x => x = μ₂) (fun a => (f a).trans fun a => p a ⋆ fun x => x = μ₂) _ _ this
      intro a
      simp[HPredTrans.sep_conj_stuff]
  }

instance HPredTrans.instMonad : Monad HPredTrans where
  pure := HPredTrans.pure
  bind := HPredTrans.bind

instance HPredTrans.instLawfulMonad : LawfulMonad HPredTrans where
  bind_pure_comp := by simp[Bind.bind, Pure.pure, Functor.map, Function.comp_def]
  pure_bind := by intros; ext p; simp[Bind.bind, Pure.pure, HPredTrans.bind, HPredTrans.pure]
  bind_assoc := by intros; ext p; simp [Bind.bind, HPredTrans.bind]
  bind_map := by intros; ext p; simp [Bind.bind, HPredTrans.bind, Functor.map, Function.comp_apply, HPredTrans.pure, Seq.seq]
  map_pure := by intros; ext p; simp [Bind.bind, HPredTrans.bind, Pure.pure, HPredTrans.pure, Functor.map, Function.comp_apply]
  map_const := sorry
  id_map := sorry
  pure_seq := sorry
  seqLeft_eq := sorry
  seqRight_eq := sorry

-- observe incr = fun q s => q () (s + 1)
-- { s := 0 } incr {(), s := 1}
-- = (fun s => s = 0) → observe incr fun () s => s = 1
-- = (fun s => s = 0) → fun s => (fun () s => (s = 1)) () (s + 1)
--
-- Insight: It is likely that all interesting observations are of the form
--   fun q xs => f xs ⊆ q
-- for vanilla PredTrans, this is just post.
-- for StateT σ PredTrans, this is `fun q s => (a,s') ∈ f s → q a s'`
-- for HPredTrans, this is `fun q μ => (a, μ') ∈ f μ → q a μ'`

def HPredTrans.select (f : Heap → α → HProp) : HPredTrans α :=
  { trans := fun q μ => ∀(frame : HProp), ∃ μ₁ μ₂, μ₁.Disjoint μ₂ ∧ μ = μ₁ ∪ μ₂ ∧ ∀ a μ₁', μ₁'.Disjoint μ₂ → f μ₁ a μ₁' → frame μ₂ → q a (μ₁' ∪ μ₂),
    mono := by
      intro _ _ hpq μ hp frame
      obtain ⟨μ₁,μ₂,hdis,hunion,hp⟩ := hp frame
      use μ₁, μ₂, hdis, hunion
      intro a μ₁' hdis' hf hframe
      exact hpq _ _ (hp a μ₁' hdis' hf hframe)
    frame := by
      intro q frame₁ μ h frame₂
      simp at h
      obtain ⟨μ₁, μ₂, hdis, hunion, h, hframe₁⟩ := h
      obtain ⟨μ₁₁, μ₁₂, hdis₁, hunion₁, h⟩ := h (fun μ₁₂ => frame₂ (μ₁₂ ∪ μ₂)) --(frame₁ -⋆ frame₂)
      have hdis' : μ₁₁.Disjoint (μ₁₂ ∪ μ₂) := sorry -- follows from hdis₁ : μ₁₁.Disjoint μ₁₂, hdis : (μ₁₁ ∪ μ₁₂).Disjoint μ₂
      have hunion' : μ = μ₁₁ ∪ (μ₁₂ ∪ μ₂) := sorry -- follows from hunion₁ : μ₁ = μ₁₁ ∪ μ₁₂ and hunion : μ₁ ∪ μ₂ = μ
      use μ₁₁, (μ₁₂ ∪ μ₂), hdis', hunion'
      intro a μ₁' hdis₁' hf hframe₂
      have hdis₂' : μ₁'.Disjoint μ₁₂ := sorry -- follows from hdis₁' : μ₁'.Disjoint (μ₁₂ ∪ μ₂)
      apply HProp.sep_conj_intro.mpr
      have hassoc : μ₁' ∪ (μ₁₂ ∪ μ₂) = μ₁' ∪ μ₁₂ ∪ μ₂ := sorry -- associativity of ∪
      have hdis₃' : (μ₁' ∪ μ₁₂).Disjoint μ₂ := sorry -- follows from hdis₁' : μ₁'.Disjoint (μ₁₂ ∪ μ₂)
      use (μ₁' ∪ μ₁₂), μ₂, h a μ₁' hdis₂' hf hframe₂
  }

def HPredTrans.pure' (a : α) : HPredTrans α :=
  HPredTrans.select (fun μ a' μ' => μ = μ' ∧ a = a')

theorem HPredTrans.pure'_pure : HPredTrans.pure' a = HPredTrans.pure a := by
  ext q μ
  simp[HPredTrans.pure',HPredTrans.pure, HPredTrans.select]
  constructor
  · intro h
    obtain ⟨μ₁,μ₂,hdis,hunion,h⟩ := h HProp.True
    replace h :=  h a μ₁ hdis rfl rfl
    simp[hunion,h]
  · intro h frame
    use μ, Heap.empty, sorry, sorry
    intro a _ hdis' hμ ha hframe
    subst hμ ha
    simp[h]

def HPredTrans.bind' {α β} (x : HPredTrans α) (f : α → HPredTrans β) : HPredTrans β :=
  HPredTrans.select (fun μ b₁ μ₁' => x.trans (fun a => (f a).trans (fun b₂ μ₂' => b₁ = b₂ ∧ μ₁' = μ₂')) μ)

theorem HPredTrans.blah : bind' (select s) f = select (fun μ b₁ μ₁' => ∀ a μ', s μ a μ' → (f a).trans (fun b₂ μ₂' => b₁ = b₂ ∧ μ₁' = μ₂') μ') := by
  simp only [HPredTrans.bind',HPredTrans.select]
  simp only [forall_exists_index, and_imp, mk.injEq]
  ext p μ
  constructor
  · intro h frame₁
    obtain ⟨μ₁,μ₂,hdis,hunion,h⟩ := h frame₁
    use μ₁, μ₂, hdis, hunion
    intro b₁ μ₁' hdis' hsf hframe₁
    refine h b₁ μ₁' hdis' ?_ hframe₁
    clear h
    intro frame₂
    use μ₁, Heap.empty, (by simp), (by simp)
    intro a₂ μ₁' _ hs' hframe₂
    apply hsf
    simp[hs']
  · intro h frame₁
    obtain ⟨μ₁,μ₂,hdis,hunion,h⟩ := h frame₁
    use μ₁, μ₂, hdis, hunion
    intro b₁ μ₁' hdis' hsf hframe₁
    obtain ⟨μ₁'',μ₂'', hdis'', hunion'', hsf⟩ := hsf frame₁
    refine h _ μ₁' hdis' ?_ hframe₁
    clear h
    intro a₁ μ₁''' hs
    have := hsf a₁ μ₁'''
    simp[hs']


theorem HPredTrans.bind'_bind : bind' (select s) (select ∘ f) = bind (select s) (select ∘ f) := by
  ext q μ
--  generalize h : HPredTrans.select s = x
--  rw (occs := .pos [2]) [HPredTrans.select]
  simp only [bind', bind, select]
--  rw (occs := .pos [1]) [HPredTrans.select]
--  simp[HPredTrans.select, HPredTrans.bind]
--  subst h
  constructor
  · intro h frame₁
    obtain ⟨μ₁,μ₂,hdis,hunion,h⟩ := h frame₁
    use μ₁, μ₂, hdis, hunion
    intro a μ₁' hdis' hs hframe₁
    simp[select]
    intro frame₂
    use μ₁', μ₂, hdis', (by rfl)
    intro b μ₁'' hdis'' hf hframe₂
    apply h b μ₁'' hdis'' ?_ hframe₁
    intro frame₃
    use μ₁, μ₂, hdis, hunion
    simp[select]
    replace h :=  h _ μ₁ hdis
    simp[hunion,h]
  · intro h frame
    use μ, Heap.empty, sorry, sorry
    intro a _ hdis' hμ ha hframe
    subst hμ ha
    simp[h]

def HPredTrans.select2 (f : Heap → α → HProp) : HPredTrans α :=
  { trans := fun q μ => ∃(frame : HProp), ∃ μ₁ μ₂, μ₁.Disjoint μ₂ ∧ μ = μ₁ ∪ μ₂ ∧ ∀ a μ₁', μ₁'.Disjoint μ₂ → f μ₁ a μ₁' → frame μ₂ → q a (μ₁' ∪ μ₂),
    mono := by
      intro _ _ hpq μ hp
      intro a μ' hpost
      exact hpq a μ' (hp a μ' hpost)
    frame := by
      intro q frame₁ μ h
      simp at h
      obtain ⟨μ₁, μ₂, hdis, hunion, ⟨frame₂, μ₁₁, μ₁₂, hdis₁, hunion₁, h⟩, hframe₁⟩ := h
      have hdis' : μ₁₁.Disjoint (μ₁₂ ∪ μ₂) := sorry -- follows from hdis₁ : μ₁₁.Disjoint μ₁₂, hdis : (μ₁₁ ∪ μ₁₂).Disjoint μ₂
      have hunion' : μ = μ₁₁ ∪ (μ₁₂ ∪ μ₂) := sorry -- follows from hunion₁ : μ₁ = μ₁₁ ∪ μ₁₂ and hunion : μ₁ ∪ μ₂ = μ
      use (frame₁ ⋆ frame₂), μ₁₁, (μ₁₂ ∪ μ₂), hdis', hunion'
      intro a μ₁' hdis₁' hf hframe
      have hdis₂' : μ₁'.Disjoint μ₁₂ := sorry -- follows from hdis₁' : μ₁'.Disjoint (μ₁₂ ∪ μ₂)
      apply HProp.sep_conj_intro.mpr
      have hassoc : μ₁' ∪ (μ₁₂ ∪ μ₂) = μ₁' ∪ μ₁₂ ∪ μ₂ := sorry -- associativity of ∪
      have hdis₃' : (μ₁' ∪ μ₁₂).Disjoint μ₂ := sorry -- follows from hdis₁' : μ₁'.Disjoint (μ₁₂ ∪ μ₂)
      use (μ₁' ∪ μ₁₂), μ₂, h a μ₁' hdis₂' hf ?hframe
  }

def PredTrans.toSep (x : PredTrans α) : HPredTrans α :=
  { trans := fun q μ => (x.val (fun a => q a μ)),
    mono := by intro _ _ hpq μ; simp; exact x.property _ _ (fun a => hpq a μ)
    frame := by
      intro μ₁ μ₂ p hdis
      simp_all[HProp.sep_conj_intro]
      intro hp
      apply x.property _ _ _ hp
      intro a hp
      use μ₁
  }

theorem HPredTrans.PredTrans_pure_pure :
  HPredTrans.pure x = PredTrans.toSep (PredTrans.pure x) := by
  ext p μ
  simp only [pure, persistent_elim, forall_eq, PredTrans.toSep, PredTrans.pure]

theorem HPredTrans.PredTrans_bind_bind :
  HPredTrans.bind (PredTrans.toSep x) (fun a => PredTrans.toSep (f a))
  = PredTrans.toSep (PredTrans.bind x f) := by
  simp[HPredTrans.bind, PredTrans.bind, PredTrans.toSep]

end HPredTrans

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
    intro p hyg
    apply hxy
    exact y.property _ _ (fun a => hfg a p) hyg

instance HPredTrans.instMonadOrdered : MonadOrdered HPredTrans where
  bind_mono := by
    intros _ _ x y f g hxy hfg
    simp[Bind.bind,HPredTrans.bind] at *
    intro p μ hyg
    apply hxy
    exact y.mono _ _ (fun a => hfg a p) μ hyg

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
  observe := ExceptT.observe
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

def HPredTrans.Triple [Monad m] [Observation m HPredTrans] (P : HProp) (x : m α) (Q : α → HProp) : Prop :=
  ∀ μ, (P -⋆ (Observation.observe x).trans Q) μ

end Observation

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
  observe := fun x => Pure.pure x.run
  pure_pure := by simp[Pure.pure, pure, implies_true]
  bind_bind := by simp only [Bind.bind, bind, ↓pure_bind, implies_true]

theorem Idd.observe_run {p : α → Prop} {e : Idd α} : (Observation.observe (w := PredTrans) (e : Idd α)).val p ↔ p e.run := by rfl

theorem Idd.observe_nf : Observation.observe (e : Idd α) = Pure.pure e.run := by rfl

theorem Idd.observe_post : Observation.observe (e : Idd α) ≤ PredTrans.post p ↔ p e.run := by
  simp only [Observation.observe, PredTrans.le_pure_post]

theorem Idd.observe_push_post : Observation.observe (e : Idd α) ≤ PredTrans.post p ↔ (Observation.observe (e : Idd α)).val p := by
  rw [Idd.observe_post, Idd.observe_run]

end Idd

section Triple

inductive TransStack : Type 1 where
  | pure : TransStack
  | state : (σ : Type) → TransStack → TransStack
  | except : (ε : Type) → TransStack → TransStack

@[reducible]
def PreCond : TransStack → Type → Type
  | .pure => Id
  | .state σ s => ReaderT σ (PreCond s)
  | .except _ s => PreCond s

@[reducible]
def FailConds : TransStack → Type
  | .pure => Unit
  | .state σ s => FailConds s
  | .except ε s => (ε → PreCond s Prop) × FailConds s

-- Translate a transformer stack to a multi-barreled postcondition
@[reducible]
def PostCond (α : Type) (s : TransStack) (r : Type) : Type :=
  (α → PreCond s r) × FailConds s

open TransStack in
example {ρ ε σ} : PreCond (state σ (state ρ (except ε pure))) Prop = (σ → ρ → Prop) := rfl

section PostCondExamples
open TransStack

variable (α ρ ε ε₁ ε₂ σ σ₁ σ₂ : Type)
#reduce (types:=true) PostCond α (except ε₂ (state σ₂ (except ε₁ (state σ₁ pure)))) ρ
-- at one point I also had TransStack.reader, but it's simpler to implement it as state
-- because then we can turn a precondition into a postcondition without complicated traversals.
-- Same for writer (presumably).
example : PostCond α (state ρ pure) Prop = ((α → ρ → Prop) × Unit) := rfl
example : PostCond α (except ε pure) Prop = ((α → Prop) × (ε → Prop) × Unit) := rfl
example : PostCond α (state σ (except ε pure)) Prop = ((α → σ → Prop) × (ε → Prop) × Unit) := rfl
example : PostCond α (except ε (state σ₁ pure)) Prop = ((α → σ₁ → Prop) × (ε → σ₁ → Prop) × Unit) := rfl
example : PostCond α (state σ₂ (except ε (state σ₁ pure))) Prop = ((α → σ₂ → σ₁ → Prop) × (ε → σ₁ → Prop) × Unit) := rfl
example : PostCond α (except ε₂ (state σ₂ (except ε₁ (state σ₁ pure)))) Prop = ((α → σ₂ → σ₁ → Prop) × (ε₂ → σ₂ → σ₁ → Prop) × (ε₁ → σ₁ → Prop) × Unit) := rfl
example : PostCond α (except ε₂ (state σ₂ (except ε₁ (state σ₁ pure)))) β = ((α → σ₂ → σ₁ → β) × (ε₂ → σ₂ → σ₁ → Prop) × (ε₁ → σ₁ → Prop) × Unit) := rfl

-- #reduce (types := true) ((do pure ((← MonadReaderOf.read) < 13 ∧ (← MonadReaderOf.read) = "hi")) : PreCond (state Nat (state String pure)) Prop)

end PostCondExamples

instance PreCond.instMonad : {stack : TransStack} → Monad (PreCond stack)
  | .pure => (inferInstance : Monad Id)
  | .state σ s => let _ := @instMonad s; (inferInstance : Monad (ReaderT σ (PreCond s)))
  | .except ε s => @instMonad s

noncomputable instance PreCond.instLattice : {stack : TransStack} → CompleteLattice (PreCond stack Prop)
  | .pure => ((inferInstance : CompleteLattice Prop) : CompleteLattice (PreCond .pure Prop))
  | .state σ s => let _ := @instLattice s; (inferInstance : CompleteLattice (σ → PreCond s Prop))
  | .except ε s => @instLattice s

noncomputable instance PreCond.instPreorder {stack : TransStack} : Preorder (PreCond stack Prop) := inferInstance
noncomputable instance PreCond.instLE {stack : TransStack} : LE (PreCond stack Prop) := inferInstance

def FailConds.const (p : Prop) : FailConds stack :=
  match stack with
  | .pure => ()
  | .state σ s => @FailConds.const s p
  | .except ε s => (fun _ε => pure p, @FailConds.const s p)

def FailConds.true : FailConds stack := FailConds.const True
def FailConds.false : FailConds stack := FailConds.const False

noncomputable instance FailConds.instPreorder : {stack : TransStack} → Preorder (FailConds stack)
  | .pure => inferInstance
  | .state _ s => let _ := @instPreorder s; inferInstance
  | .except _ s => let _ := @instPreorder s; inferInstance

-- instance FailConds.instLE {stack : TransStack} : LE (FailConds stack) := FailConds.instPreorder.toLE

noncomputable instance PostCond.instPreorder : {stack : TransStack} → Preorder (PostCond α stack Prop) := inferInstance
noncomputable instance PostCond.instLE {stack : TransStack} : LE (PostCond α stack Prop) := inferInstance

@[simp]
lemma PreCond.bot_le {x : PreCond stack Prop} : pure False ≤ x := by
  induction stack
  case pure => exact False.elim
  case state σ s ih => intro; exact ih
  case except ε s ih => exact ih

@[simp]
lemma PreCond.le_top {x : PreCond stack Prop} : x ≤ pure True := by
  induction stack
  case pure => exact fun _ => True.intro
  case state σ s ih => intro; exact ih
  case except ε s ih => exact ih

@[simp]
lemma FailConds.bot_le {x : FailConds stack} : FailConds.false ≤ x := by
  simp only [false]
  induction stack
  case pure => simp
  case state σ s ih => exact ih
  case except ε s ih => simp only [const, Prod.le_def, ih, and_true]; intro ε; exact PreCond.bot_le

@[simp]
lemma FailConds.le_top {x : FailConds stack} : x ≤ FailConds.true := by
  simp only [true]
  induction stack
  case pure => simp
  case state σ s ih => exact ih
  case except ε s ih => simp only [const, Prod.le_def, ih, and_true]; intro ε; exact PreCond.le_top

-- A postcondition expressing total correctness
def PostCond.total (p : α → PreCond stack β) : PostCond α stack β :=
  (p, FailConds.false)

-- A postcondition expressing partial correctness
def PostCond.partial (p : α → PreCond stack β) : PostCond α stack β :=
  (p, FailConds.true)

@[simp]
lemma PostCond.total_fst : (PostCond.total p).1 = p := by rfl
@[simp]
lemma PostCond.partial_fst : (PostCond.partial p).1 = p := by rfl

@[simp]
lemma PostCond.total_snd : (PostCond.total p).2 = FailConds.false := by rfl
@[simp]
lemma PostCond.partial_snd : (PostCond.partial p).2 = FailConds.true := by rfl

@[simp]
lemma PostCond.total_def {p : α → PreCond stack β} : (p, FailConds.false) = PostCond.total p := rfl
@[simp]
lemma PostCond.partial_def {p : α → PreCond stack β} : (p, FailConds.true) = PostCond.partial p := rfl

@[simp]
lemma PostCond.le_total (p q : α → PreCond stack Prop) : PostCond.total p ≤ PostCond.total q ↔ ∀ a, p a ≤ q a := by
  simp only [total, Prod.le_def, le_refl, and_true]
  rfl

@[simp]
lemma PostCond.le_partial (p q : α → PreCond stack Prop) : PostCond.partial p ≤ PostCond.partial q ↔ ∀ a, p a ≤ q a := by
  simp only [PostCond.partial, Prod.le_def, le_refl, and_true]
  rfl

-- notation "test[ s < 13]" => (do pure ((← read) < 13))
syntax "test[" hygieneInfo term "]" : term
macro_rules
| `(test[ $hy:hygieneInfo $e ]) => do
  -- Replace all occurrences of `s` with `(← MonadReaderOf.read)`
  let s := HygieneInfo.mkIdent hy `s (canonical := true)
  let e' ← e.replaceM fun
    | `($x:ident) => if s.getId = x.getId then `(← MonadReaderOf.read) else pure none
    | _ => pure none
  `(do pure $e')

#check test[s < 13 ∧ s = "hi"]

class MonadTriple (m : Type → Type) (stack : outParam TransStack) where
  triple (x : m α) (P : PreCond stack Prop) (Q : PostCond α stack Prop) : Prop
open MonadTriple (triple)

instance Idd.instMonadTriple : MonadTriple Idd .pure where
  triple {α} (x : Idd α) (P : Prop) (Q : (α → Prop) × Unit) := P ≤ Q.1 x.run

-- universe error due to Heap : Type 1:
--instance HPredTrans.instMonadTriple' : MonadTriple' HPredTrans [Heap] [] where
--  triple x (P : Prop) Q := P ≤ x.val Q

instance StateT.instMonadTriple [Monad m] [MonadTriple m stack] : MonadTriple (StateT σ m) (.state σ stack) where
  triple x P Q :=
     ∀ s, MonadTriple.triple (x s) (P s) (fun (a, s') => Q.1 a s', Q.2)

instance ReaderT.instMonadTriple [Monad m] [MonadTriple m stack] : MonadTriple (ReaderT ρ m) (.state ρ stack) where
  triple x P Q :=
     ∀ r, MonadTriple.triple (x r) (P r) (fun a => Q.1 a r, Q.2) -- NB: Q.1 gets passed r as well; simpler that way

#reduce (types:=true) StateT Bool (Except Int) String
#reduce (types:=true) ExceptT Int (StateM Bool) String
#reduce (types:=true) StateT Char (ExceptT Int (StateM Bool)) String

instance ExceptT.instMonadTriple [MonadTriple m stack] : MonadTriple (ExceptT ε m) (.except ε stack) where
  triple {α} (x : ExceptT ε m α) (P : PreCond (.except ε stack) Prop) (Q : PostCond α (.except ε stack) Prop) :=
    MonadTriple.triple (stack:=stack) x.run P (fun | .ok a => Q.1 a | .error e => Q.2.1 e, Q.2.2)

instance EStateM.instMonadTriple : MonadTriple (EStateM ε σ) (.except ε (.state σ .pure)) where
  triple {α} (x : EStateM ε σ α) (P : PreCond (.except ε (.state σ .pure)) Prop) (Q : PostCond α (.except ε (.state σ .pure)) Prop) :=
    ∀ s, P s → match x s with
      | .ok a s'    => Q.1 a s'
      | .error e s' => Q.2.1 e s'

class LawfulMonadTriple (m : Type → Type) (stack : outParam TransStack)
  [Monad m] [LawfulMonad m] [MonadTriple m stack] where
  triple_conseq {P P' : PreCond stack Prop} {Q Q' : PostCond α stack Prop} (x : m α)
    (hp : P ≤ P' := by simp) (hq : Q' ≤ Q := by simp)
    (h : triple x P' Q') :
    triple x P Q
  triple_extract_persistent {P : Prop} {P' : PreCond stack Prop} {Q : PostCond α stack Prop}
    (x : m α) (h : P → triple x P' Q) :
    triple x (pure P ⊓ P') Q
  triple_pure {α} {Q : PostCond α stack Prop} (a : α) (himp : P ≤ Q.1 a):
    triple (pure (f:=m) a) P Q
  triple_bind {α β} {Q : PostCond α stack Prop} {R : PostCond β stack Prop} (x : m α) (f : α → m β)
    (hx : triple x P Q) (herror : Q.2 ≤ R.2 := by simp)
    (hf : ∀ b, triple (f b) (Q.1 b) R) :
    triple (x >>= f) P R

theorem LawfulMonadTriple.triple_map {m : Type → Type} [Monad m] [LawfulMonad m] [MonadTriple m stack] [LawfulMonadTriple m stack] (f : α → β) (x : m α)
  (h : triple x P (fun a => Q.1 (f a), Q.2)) :
  triple (f <$> x) P Q := by
    simp only [← bind_pure_comp]
    apply triple_bind _ _ h
    intro b
    apply triple_pure
    simp only [le_refl]

theorem LawfulMonadTriple.triple_seq {m : Type → Type} [Monad m] [LawfulMonad m] [MonadTriple m stack] [LawfulMonadTriple m stack] (f : m (α → β)) (x : m α)
  (hf : triple f P Q) (herror : Q.2 ≤ R.2 := by simp)
  (hx : ∀ f, triple x (Q.1 f) (fun a => R.1 (f a), R.2)) :
  triple (f <*> x) P R := by
    simp only [← bind_map]
    apply triple_bind _ _ hf herror ?_
    intro f
    apply triple_map _ _ (hx f)

theorem LawfulMonadTriple.triple_extract_persistent_true {m : Type → Type} [Monad m] [LawfulMonad m] [MonadTriple m stack] [LawfulMonadTriple m stack] {P : Prop} {Q : PostCond α stack Prop}
  (x : m α) (h : P → triple x (pure True) Q) :
  triple x (pure P) Q := by
    have : pure P = (pure P ⊓ pure True : PreCond stack Prop) := by simp
    rw[this]
    exact triple_extract_persistent x h

open LawfulMonadTriple

instance Idd.instLawfulMonadTriple : LawfulMonadTriple Idd .pure where
  triple_conseq x hp' hq h := by intro; apply_rules [(Prod.le_def.mp hq).1]
  triple_extract_persistent x h := by intro hp; exact (h hp.1) hp.2
  triple_pure _ himp := by simp[triple, Pure.pure, Idd.pure, himp]
  triple_bind x f hspec herror hrest := by
    simp_all only [triple, le_Prop_eq, le_refl, Bind.bind, bind, implies_true]

instance StateT.instLawfulMonadTriple [Monad m] [LawfulMonad m] [MonadTriple m stack] [LawfulMonadTriple m stack] :
  LawfulMonadTriple (StateT σ m) (.state σ stack) where
  triple_conseq x hp hq h := by
    intro s
    apply triple_conseq (x s) (hp s) ?_ (h s)
    constructor
    · intro (a, s')
      exact hq.1 a s'
    · exact hq.2
  triple_extract_persistent x h := by
    intro s
    apply triple_extract_persistent (x s) (fun hp => h hp s)
  triple_pure _ himp := by
    intro s
    apply LawfulMonadTriple.triple_pure
    exact (himp s)
  triple_bind x f hspec herror hrest := by
    simp_all only [triple, bind, StateT.bind]
    intros
    apply_rules [LawfulMonadTriple.triple_bind, hspec]
    intros
    apply hrest

instance ReaderT.instLawfulMonadTriple [Monad m] [LawfulMonad m] [MonadTriple m stack] [LawfulMonadTriple m stack] :
  LawfulMonadTriple (ReaderT ρ m) (.state ρ stack) where
  triple_conseq x hp hq h := by
    intro r
    apply triple_conseq (x r) (hp r) ?_ (h r)
    constructor
    · intro a
      exact hq.1 a r
    · exact hq.2
  triple_extract_persistent x h := by
    intro r
    apply triple_extract_persistent (x r) (fun hp => h hp r)
  triple_pure _ himp := by
    intro r
    apply LawfulMonadTriple.triple_pure
    exact (himp r)
  triple_bind x f hspec herror hrest := by
    simp_all only [triple, bind, ReaderT.bind]
    intros
    apply_rules [LawfulMonadTriple.triple_bind, hspec]
    intros
    apply hrest

instance ExceptT.instLawfulMonadTriple [Monad m] [LawfulMonad m] [MonadTriple m stack] [LawfulMonadTriple m stack] :
  LawfulMonadTriple (ExceptT ε m) (.except ε stack) where
  triple_conseq x hp hq h := by
    simp_all [triple, bind, ExceptT.bind]
    apply triple_conseq (stack := stack) x.run hp ?hq h
    have h21 := (Prod.le_def.mp (Prod.le_def.mp hq).2).1
    have h22 := (Prod.le_def.mp (Prod.le_def.mp hq).2).2
    exact ⟨fun | Except.ok a => (Prod.le_def.mp hq).1 a | Except.error e => h21 e, h22⟩
  triple_extract_persistent x h := by
    apply triple_extract_persistent (stack := stack) x.run (fun hp => h hp)
  triple_pure _ himp := by
    simp only [triple, pure, ExceptT.pure, run_mk]
    apply LawfulMonadTriple.triple_pure
    exact himp
  triple_bind x f hspec herror hrest := by
    simp_all only [triple, bind, ExceptT.bind]
    apply_rules [LawfulMonadTriple.triple_bind]
    · intro b
      cases b
      case error a =>
        apply LawfulMonadTriple.triple_pure
        simp only [ExceptT.bindCont]
        exact (Prod.le_def.mp herror).1 a
      case ok a =>
        simp only [ExceptT.bindCont]
        exact hrest a
    · exact (Prod.le_def.mp herror).2

notation:lead "⦃" P "⦄ " x:lead " ⦃" Q "⦄" =>
  MonadTriple.triple x P Q
notation:lead "⦃" P "⦄ " x:lead " ⦃" v ", " Q "⦄" =>
  ⦃P⦄ x ⦃PostCond.total fun v => Q⦄

theorem Triple.forIn_list {α β} {m : Type → Type}
  [Monad m] [LawfulMonad m] [MonadTriple m stack] [LawfulMonadTriple m stack]
  {xs : List α} {init : β} {f : α → β → m (ForInStep β)} {P : PreCond stack Prop} {Q : PostCond β stack Prop}
  (inv : List α → β → PreCond stack Prop)
  (hpre : P ≤ inv xs init)
  (hpost : inv [] ≤ Q.1)
  (hstep : ∀ hd tl b,
      ⦃inv (hd :: tl) b⦄
      (f hd b)
      ⦃r, match r with | .yield b' => inv tl b' | .done b' => inv [] b'⦄) :
  ⦃P⦄ (forIn xs init f) ⦃Q⦄ := by
    replace hpost : PostCond.total (inv []) ≤ Q := by simp[Prod.le_def, hpost]
    apply triple_conseq _ hpre hpost
    clear hpre hpost
    induction xs generalizing init
    case nil => apply LawfulMonadTriple.triple_pure; simp
    case cons hd tl ih =>
      simp only [List.forIn_cons]
      apply LawfulMonadTriple.triple_bind
      case hx => exact hstep hd tl init
      case herror => simp
      case hf =>
        intro b
        split
        · apply LawfulMonadTriple.triple_pure; simp
        · exact ih

theorem Triple.foldlM_list {α β} {m : Type → Type}
  [Monad m] [LawfulMonad m] [MonadTriple m stack] [LawfulMonadTriple m stack]
  {xs : List α} {init : β} {f : β → α → m β} {P : PreCond stack Prop} {Q : PostCond β stack Prop}
  (inv : List α → β → PreCond stack Prop)
  (hpre : P ≤ inv xs init := by simp)
  (hpost : inv [] ≤ Q.1 := by simp)
  (hstep : ∀ hd tl b,
      ⦃inv (hd :: tl) b⦄
      (f b hd)
      ⦃b', inv tl b'⦄) :
  ⦃P⦄ (List.foldlM f init xs) ⦃Q⦄ := by
  have : xs.foldlM f init = forIn xs init (fun a b => .yield <$> f b a) := by
    simp only [List.forIn_yield_eq_foldlM, id_map']
  rw[this]
  apply Triple.forIn_list inv hpre hpost
  intro hd tl b
  apply LawfulMonadTriple.triple_map _ _ (hstep hd tl b)

end Triple

section IO

axiom IO.satisfies_post {α ε} (x : EIO ε α) (p : Except ε α → Prop) : Prop
axiom IO.satisfies_conseq {α ε} {x : EIO ε α} {Q Q' : Except ε α → Prop} :
  Q ≤ Q' → IO.satisfies_post x Q → IO.satisfies_post x Q'
axiom IO.satisfies_pure {α ε} {Q : Except ε α → Prop} (a : α) (h : Q (.ok a)) :
  IO.satisfies_post (pure a) Q
axiom IO.satisfies_bind {α β ε} {P : Except ε α → Prop} {Q : Except ε β → Prop} {x : EIO ε α} {f : α → EIO ε β}
  (hx : IO.satisfies_post x P)
  (herror : ∀ e, P (.error e) → Q (.error e))
  (hf : ∀ a, P (.ok a) → IO.satisfies_post (f a) Q) :
  IO.satisfies_post (x >>= f) Q

instance IO.instMonadTriple : MonadTriple (EIO ε) (.except ε .pure) where
  triple x P Q :=
    P → IO.satisfies_post x (fun | .ok a => Q.1 a | .error e => Q.2.1 e)

instance IO.instLawfulMonadTriple : LawfulMonadTriple (EIO ε) (.except ε .pure) where
  triple_conseq x hp' hq h := by
    intro hp
    apply IO.satisfies_conseq ?_ (h (hp' hp))
    intro x; cases x <;> apply_rules[hq.1, hq.2.1]
  triple_extract_persistent x h := by intro hp; exact (h hp.1) hp.2
  triple_pure _ himp := by intro hp; apply IO.satisfies_pure; exact (himp hp)
  triple_bind x f hspec herror hrest := by
    intro hp
    apply IO.satisfies_bind (hspec hp) _ hrest
    exact herror.1

/-- Backward predicate transformer derived from a substitution property of monads.
A generic effect observation that can be used to observe many monads.
It is a suitable choice for the opaque base layer of a specification monad stack, such as for `IO`.
-/
def Subst {m : Type u → Type v} {α} [Monad m] (x : m α) : PredTrans α :=
  ⟨fun p => ∀ {β} {f g : α → m β}, (∀ a, p a → f a = g a) → x >>= f = x >>= g, fun _ _ hpq hsubst _ _ _ hfg => hsubst fun a hp => hfg a (hpq a hp)⟩
-- urgh, cannot prove this direction of bind_bind: Subst (x >>= f) ≤ Subst x >>= fun a => Subst (f a)
-- Specifically,
-- α β : Type
-- x : IO α
-- f : α → IO β
-- p : β → Prop
-- h✝ : ↑(Subst (x >>= f)) p
-- β✝ : Type
-- g h : α → IO β✝
-- hgh : ∀ (a : α), ↑(Subst (f a)) p → g a = h a
-- ⊢ x >>= g = x >>= h
-- It appears we need to derive from hgh that g and h factor over f.

theorem Subst.conj [Monad m] [LawfulMonad m] {x : m α}
    (hp : (Subst x).val p) (hq : (Subst x).val q) : (Subst x).val (fun r => p r ∧ q r) := by
  intros β f g hfg
  open Classical in
  calc x >>= f
    _ = x >>= (fun r => if p r ∧ q r then f r else f r) := by simp
    _ = x >>= (fun r => if p r ∧ q r then g r else f r) := by simp +contextual [hfg]
    _ = x >>= (fun r => if q r then g r else f r) := hp (by simp +contextual)
    _ = x >>= g := hq (by simp +contextual)

theorem Subst.subst [Monad m] [LawfulMonad m] {x : m α}
  (hk : ∀ {β} {f g : α → m β}, (∀ a, p a → f a = g a))
  (hsub : Subst x ≤ PredTrans.post p) :
  x >>= f = x >>= g :=
  hsub p (le_refl _) hk

@[simp]
theorem EStateM.pure_inj [inh : Inhabited σ] : pure (f := EStateM ε σ) x = pure y ↔ x = y := by
  constructor
  case mp =>
    intro h
    injection congrArg (·.run inh.default) h
  case mpr => intro h; simp[h]

@[simp]
axiom IO.pure_inj {α} {x y : α} : pure (f := IO) x = pure y ↔ x = y -- just as for EStateM, but unsafe. Yet very reasonable; part of the TCB

axiom IO.observe {α} (x : IO α) : HPredTrans α
axiom IO.observe_pure {α} {x : α} : IO.observe (pure x) = HPredTrans.pure x
axiom IO.observe_bind {α β} (x : IO α) (f : α → IO β) : IO.observe (x >>= f) = IO.observe x >>= fun a => IO.observe (f a)

set_option pp.universes true in
noncomputable instance IO.instObservation : Observation IO HPredTrans where
  observe := IO.observe
  pure_pure := IO.observe_pure
  bind_bind x f := IO.observe_bind x f

end IO

gen_injective_theorems% ForInStep

-- the following two lemmas are actually a bit ineffective because post_bind_pure
-- wins when a and b are representable by post. Also, often it's not a plain map
-- but rather `fun a => .yield (a + hd)`, and then we would need to exploit general
-- injectivity.
@[simp]
theorem PredTrans.ForInStep_yield_cancel {a b : PredTrans α} : ForInStep.yield <$> a ≤ ForInStep.yield <$> b ↔ a ≤ b := by
  constructor
  case mp =>
    intro h p
    replace h := h (fun s => ∃ a, s = .yield a ∧ p a)
    simp[←bind_pure_comp, Pure.pure, pure, Bind.bind, bind] at h
    exact h
  case mpr =>
    intro h p
    simp[←bind_pure_comp, Pure.pure, pure, Bind.bind, bind]
    exact h (fun a => p (.yield a))

@[simp]
theorem PredTrans.ForInStep_done_cancel {a b : PredTrans α} : ForInStep.done <$> a ≤ ForInStep.done <$> b ↔ a ≤ b := by
  constructor
  case mp =>
    intro h p
    replace h := h (fun s => ∃ a, s = .done a ∧ p a)
    simp[←bind_pure_comp, Pure.pure, pure, Bind.bind, bind] at h
    exact h
  case mpr =>
    intro h p
    simp[←bind_pure_comp, Pure.pure, pure, Bind.bind, bind]
    exact h (fun a => p (.done a))

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

theorem test_3 : Observation.observe (do let mut x := 0; for i in [1:5] do { x := x + i }; pure (f := Idd) (); return x) ≤ PredTrans.post (· < 30) := by
  simp
  apply le_trans (Observation.forIn_list ?inv ?hpre ?hstep) ?hgoal
  case inv => exact fun xs => PredTrans.post fun r => (∀ x, x ∈ xs → x ≤ 5) ∧ r + xs.length * 5 ≤ 25
  case hpre => simp_arith
  case hstep => simp_arith; intro hd tl; left; intro r x h h1 h2; subst h; simp_all; omega
  case hgoal => simp_arith

theorem test_3_2 : Observation.observe (do let mut x := 0; for i in [1:5] do { x := x + i }; pure (f := Idd) (); return x) ≤ pure 10 := by
  simp
  apply le_trans (Observation.forIn_list ?inv ?hpre ?hstep) ?hgoal
  case inv => exact fun xs => PredTrans.post fun r => r + xs.sum = 10
  case hpre => simp_arith
  -- sigh. the following could be much better! TODO
  case hstep => simp_arith; intro hd tl; left; intro r x h h1; subst h; simp_all
  case hgoal => simp

-- TBD: Figure out while loops
theorem test_4 : Observation.observe (do let mut x := 0; let mut i := 0; while i < 4 do { x := x + i; i := i + 1 }; pure (f := Idd) (); return x) ≤ pure 6 := by
  simp
  apply use_spec_map (Observation.forIn_loop ?term ?inv ?hpre ?hstep) ?hgoal
  case term => sorry
  case inv => exact PredTrans.post fun | ⟨i, x⟩ => x + (List.range' i (4-i) 1).sum = 6
  case hpre => simp_arith
  case hstep => sorry
  case hgoal => simp; sorry -- later: conv => lhs; arg 1; intro x; tactic =>

theorem test_1 : Observation.observe (do let mut id := 5; id := 3; pure (f := Idd) id) ≤ pure 3 := by
  simp

theorem test_2 : Observation.observe (do let mut x := 5; if x > 1 then { x := 1 } else { x := x }; pure (f:=Idd) x) ≤ pure 1 := by
  simp

theorem test_2_2 : Observation.observe (do let mut id := 5; id := 3; pure (f := Idd) id) ≤ PredTrans.post (· < 20) := by
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
    case inv => exact fun xs => PredTrans.post fun f_H => ∀ i j, f_H i j → 2*t-1 < dist f_H s(i,j)
    case hpre => simp
    case hstep =>
      intro e es
      apply PredTrans.bind_post; intro f_H hinv
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
  case inv => exact fun xs => PredTrans.post fun
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
  subst h
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

axiom IO.rand_spec {n : Nat} : ⦃True⦄ (IO.rand 0 n : IO Nat) ⦃r, r < n⦄

/-- The result has the same parity as the input. -/
theorem addRandomEvens_spec (n k) : ⦃True⦄ (addRandomEvens n k) ⦃r, r % 2 = k % 2⦄ := by
  let _ := (PreCond.instPreorder : Preorder (PreCond (.except IO.Error .pure) Prop))
  simp only [addRandomEvens, bind_pure_comp, map_pure, List.forIn_yield_eq_foldlM, bind_pure]
  apply Triple.foldlM_list (m := IO) (fun xs r => r % 2 = k % 2) ?hpre le_rfl ?step
  case hpre => simp
  case step =>
    intro hd tl b; dsimp
    -- ⦃b % 2 = k % 2⦄
    -- ((fun c => b + 2 * c) <$> liftM (IO.rand 0 37))
    -- ⦃PostCond.total fun b' => b' % 2 = k % 2⦄
    -- (should unexpand that to ⦃b', b' % 2 = k % 2⦄)
    apply LawfulMonadTriple.triple_extract_persistent_true; intro h; dsimp
    -- h : b % 2 = k % 2
    -- -----
    -- ⦃True⦄
    -- ((fun c => b + 2 * c) <$> liftM (IO.rand 0 37))
    -- ⦃PostCond.total fun b' => b' % 2 = k % 2⦄
    apply LawfulMonadTriple.triple_map; dsimp
    -- h : b % 2 = k % 2
    -- -----
    -- ⦃True⦄
    -- liftM (IO.rand 0 37)
    -- ⦃PostCond.total fun a => (b + 2 * a) % 2 = k % 2⦄
    apply LawfulMonadTriple.triple_conseq _ le_rfl _ IO.rand_spec; dsimp
    -- (PostCond.total fun r => r < 37) ≤ (PostCond.total fun a => (b + 2 * a) % 2 = k % 2)
    simp[PostCond.total]
    intro _ _; exact h

/-- Since we're adding even numbers to our number twice, and summing,
the entire result is even. -/
theorem program_spec (n k) : ⦃True⦄ program n k ⦃r, r % 2 = 0⦄ := by
  let _ := (PreCond.instPreorder : Preorder (PreCond (.except IO.Error .pure) Prop))
  -- unfold program
  simp[program] -- only [program, bind_pure_comp, Observation.bind_bind, Observation.map_map]
  -- apply the spec for addRandomEvens
  apply LawfulMonadTriple.triple_bind _ _ (addRandomEvens_spec n k); intro b; dsimp
  -- ⦃b % 2 = k % 2⦄
  -- HAdd.hAdd b <$> addRandomEvens n k
  -- ⦃PostCond.total fun r => r % 2 = 0⦄
  apply LawfulMonadTriple.triple_extract_persistent_true; intro h; dsimp
  -- h : b % 2 = k % 2
  -- -----
  -- ⦃True⦄
  -- HAdd.hAdd b <$> addRandomEvens n k
  -- ⦃PostCond.total fun r => r % 2 = 0⦄
  apply LawfulMonadTriple.triple_map; dsimp
  -- h : b % 2 = k % 2
  -- -----
  -- ⦃True⦄
  -- addRandomEvens n k
  -- ⦃PostCond.total fun a => (b + a) % 2 = 0⦄
  apply LawfulMonadTriple.triple_conseq _ le_rfl _ (addRandomEvens_spec n k); dsimp
  simp[PostCond.total]
  intro c h2; omega

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

@[simp]
theorem HPredTrans.Triple.persistent_sep_conj {p : Prop} {q : HProp} {x : IO α} :
  ⦃↟p ⋆ q⦄ x ⦃r⦄ ↔ p → ⦃q⦄ x ⦃r⦄ := by
  constructor
  · intro h hp μ hq; replace h := h μ; simp at h; exact h hp μ hq sorry rfl
  · intro h μ; simp; intro hp μ hq hdis hμ; subst hμ; exact h hp μ hq

@[simp]
theorem HPredTrans.Triple.exists {p : α → HProp} {x : IO β} {q : β → HProp} :
  ⦃∃' a, p a⦄ x ⦃q⦄ ↔ ∀ a, ⦃p a⦄ x ⦃q⦄ := by
  constructor
  · intro h a μ hp; exact h μ (HProp.exists_exists.mpr ⟨a, hp⟩)
  · intro h μ; simp; exact (fun a => h a μ)

@[simp]
theorem HPredTrans.map_post {f : α → β} {t : HPredTrans α} : (f <$> t).trans p = t.trans (fun a => p (f a)) := by
  sorry -- simp only [Functor.map, bind, Function.comp_apply, pure, persistent, post]

@[simp]
theorem HPredTrans.Triple.map {p : HProp} {x : IO α} {q : β → HProp} :
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

section Counter

def withNewCounter : StateT Nat Idd α → Idd α := fun s => (·.1) <$> s.run 0

def Counter.incr : StateT Nat Idd Unit := fun n => pure ((), n+1)

def Counter.get : StateT Nat Idd Nat := fun n => pure n

def test : Idd Nat := withNewCounter do
  Counter.incr
  Counter.incr
  Counter.get

theorem Counter.withNewCounter_spec {P : α → Nat → Prop}
  (h : ⦃(· = 0)⦄ m ⦃r, fun s => s = n ∧ P r n⦄) :
  ⦃True⦄ withNewCounter m ⦃r, P r n⦄ := by
  simp only [MonadTriple.triple, withNewCounter, Functor.map, Idd.bind, Function.comp_apply,
    Idd.pure, PostCond.total_fst, le_Prop_eq, forall_const]
  exact (h 0 rfl).2

theorem Counter.incr_spec : ⦃fun c => c = n⦄ Counter.incr ⦃_, fun c => c = n+1⦄ := by
  simp only [MonadTriple.triple, incr, pure, Idd.pure, PostCond.total_fst, add_left_inj, le_refl,
    implies_true]

theorem Counter.get_spec : ⦃fun c => c = n⦄ Counter.get ⦃r, fun c => c = n ∧ r = n⦄ := by
  simp only [MonadTriple.triple, get, pure, Idd.pure, Prod.fst_natCast, Nat.cast_id,
    Prod.snd_natCast, PostCond.total_fst, and_self, le_refl, implies_true]

theorem test_spec : ⦃True⦄ test ⦃r, r = 2⦄ := by
  apply Counter.withNewCounter_spec
  apply LawfulMonadTriple.triple_bind _ _ Counter.incr_spec; intro _; dsimp
  apply LawfulMonadTriple.triple_bind _ _ Counter.incr_spec; intro _; dsimp
  apply Counter.get_spec

end Counter

section HCounter

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
  apply spec Counter.new_spec (by simp); simp; intro c l hp; subst hp
  apply spec (Counter.incr_spec (n := 0)) (by simp); simp
  apply spec (Counter.incr_spec (n := 1)) (by simp); simp
  apply spec (Counter.get_spec (n := 2)) (by simp); simp
  apply Counter.free_spec

end HCounter

section NITest

def NI.embed (S : Set (σ × Set (α × σ))) : StateT σ PredTrans α := fun s =>
  ⟨fun Q => (s, Q) ∈ S, by intro p q hpq; simp; sorry⟩ -- can't show monotonicity. unsurprisingly?

def noninterference (x : StateT (Nat × Nat) Idd α) := -- fst is low, snd is high
  -- nope, this does not work out. the post condition has no means to vary σ
  StateT.instObservationState.observe x ≤ NI.embed { (σ, Q) | ∀ α₁ α₂ σ₂ σ₂', (α₁, σ₂) ∈ Q → (α₂, σ₂') ∈ Q → α₁ = α₂ }

end NITest
