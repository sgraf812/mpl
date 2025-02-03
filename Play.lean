import Lean
import VCGen.Basic
import Mathlib--.Order.CompleteLattice

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
is able to express all hyperproperties. -/
def PredTrans.post (post : α → Prop) : PredTrans α :=
  ⟨fun p => post ≤ p, fun _ _ hpq hpostp => le_trans hpostp hpq⟩

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
    intro p hyg
    apply hxy
    exact y.property _ _ (fun a => hfg a p) hyg

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
theorem Observation.map_map {m : Type u → Type v} {w : Type u → Type x} [Monad m] [LawfulMonad m] [∀{α}, Preorder (w α)] [Observation m w] {f : α → β} {x : m α} :
  observe (f <$> x) = f <$> observe x := by simp only [← bind_pure_comp, bind_bind, pure_pure]
theorem Observation.seq_seq {m : Type u → Type v} {w : Type u → Type x} [Monad m] [LawfulMonad m] [∀{α}, Preorder (w α)] [Observation m w] {f : m (α → β)} {x : m α} :
  observe (f <*> x) = observe f <*> observe x := by simp only [← bind_map, bind_bind, map_map]
attribute [simp] Observation.pure_pure Observation.bind_bind Observation.map_map Observation.seq_seq

/-- An expression's spec is a predicate transformer that is an upper bound on the observation of a program -/
abbrev Observation.Spec [Monad m] [∀{α}, Preorder (w α)] [Observation m w] (x : m α) :=
  { wp : w α // Observation.observe x ≤ wp }

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

def ExceptT.observe [Monad m] [Monad w] [∀{α}, Preorder (w α)] [base : Observation m w] (x : ExceptT ε m α) : ExceptT ε w α :=
  ExceptT.mk (base.observe (ExceptT.run x))
instance ExceptT.instObservation [Monad m] [∀{α}, Preorder (w α)] [base : Observation m w] :
  Observation (ExceptT ε m) (ExceptT ε w) where
  bind_mono := sorry
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

theorem Observation.forIn_list_no_break {α β} {m : Type u → Type v} {w : Type u → Type x}
  [Monad m] [LawfulMonad m] [∀{α}, Preorder (w α)] [obs : Observation m w]
  {xs : List α} {init : β} {f : α → β → m β}
  (inv : List α → w β)
  (hpre : pure init ≤ inv xs)
  (hstep : ∀ hd tl,
      (inv (hd :: tl) >>= fun b => obs.observe (f hd b)) ≤ inv tl) :
    obs.observe (forIn xs init (fun a b => do let r ← f a b; pure (.yield r))) ≤ inv [] :=
  Observation.forIn_list inv hpre <| by
    intro hd tl
    left
    simp only [← bind_pure_comp, bind_bind, pure_pure, ← bind_assoc, MonadOrdered.bind_mono (hstep hd tl) (by rfl)]

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

theorem Idd.observe_run : (Observation.observe (e : Idd α)).val p ↔ p e.run := by rfl

theorem Idd.observe_nf : Observation.observe (e : Idd α) = Pure.pure e.run := by rfl

theorem Idd.observe_post : Observation.observe (e : Idd α) ≤ PredTrans.post p ↔ p e.run := by
  simp only [Observation.observe, PredTrans.le_pure_post]

theorem Idd.observe_push_post : Observation.observe (e : Idd α) ≤ PredTrans.post p ↔ (Observation.observe (e : Idd α)).val p := by
  rw [Idd.observe_post, Idd.observe_run]

end Idd

section IO

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

axiom IO.observe {α} (x : IO α) : PredTrans α
axiom IO.observe_pure {α} (x : α) : IO.observe (pure x) = pure x
axiom IO.observe_bind {α β} (x : IO α) (f : α → IO β) : IO.observe (x >>= f) = IO.observe x >>= fun a => IO.observe (f a)

instance IO.instObservation : Observation IO PredTrans where
  observe := Subst
  pure_pure := by
    intro _ x
    ext p
    simp only [Subst, pure_bind]
    constructor
    · intro h
      simp only [Pure.pure, PredTrans.pure]
      open Classical in
      have h2 : pure x >>= (fun a => pure True) = pure x >>= (fun a => if p a then pure True else pure False) :=
        calc  pure x >>= (fun a => pure True)
          _ = pure x >>= (fun a => if p a then pure True else pure True) := by conv => rhs; arg 2; intro a; apply ite_self -- why doesn't simp work here???
          _ = pure x >>= (fun a => if p a then pure True else pure False) := h <| by intro a hp; simp[Pure.pure, hp]
      by_contra hnp
      simp[hnp] at h2
    · intro hp
      intro _ _ _ hfg
      simp only [hfg x hp]
  bind_bind := by
    intro α β x f
    ext p
    simp
    -- have pp x a := ∀ {γ} {g h : β → IO γ}, (∀ a, p a → g a = h a) → f a >>= g = f a >>= h
    -- have qq x a := ∀ {β} {f₁ f₂ : α → IO β}, (∀ a, pp (f a) → f₁ a = f₂ a) → x >>= f₁ = x >>= f₂
    constructor
    · intro h _ g h hfg
    have h :=
      calc (Subst x >>= (fun a => Subst (f a))).val p
        _ = (Subst x).val (fun a => (Subst (f a)).val p) := by rfl
        _ = ∀ {β} {f₁ f₂ : α → IO β}, (∀ a, (Subst (f a)).val p → f₁ a = f₂ a) → x >>= f₁ = x >>= f₂ := by rfl
        _ = (Q x (fun a => P (f a))) := by rfl
        _ = (Q x (fun a => P (f a))) := by rfl
        _ = P (x >>= f) := by rfl
        _ = (Subst (x >>= f)).val p := by rfl
    simp only [h]
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

lemma correctnessOfGreedySpanner {n:ℕ }(G : FinSimpleGraph n)(t :ℕ ) (u v : Fin n) :
  (greedySpanner G t).dist u v ≤ 2*t-1 := by
    unfold greedySpanner -- TODO: Extract the unfold+exact step into a tactic
    simp
    exact (Idd.observe_post (p := fun r => SimpleGraph.dist r u v ≤ 2*t-1)).mp <| by
      simp
      apply use_spec_map (Observation.forIn_list ?inv ?hpre ?hstep) ?hgoal
      case inv => exact fun xs => PredTrans.post fun f_H => ∀ i j, f_H i j → 2*t-1 < dist f_H s(i,j)
      case hpre => simp
      case hstep => simp; intro e; left; sorry
      case hgoal => sorry
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

macro (name := vc_spec_Idd) "vc_spec_Idd " post:term : tactic =>
  `(tactic|(apply (Idd.observe_post (p := $post)).mp; simp))

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

/-- The result has the same parity as the input. -/
theorem addRandomEvens_spec (n k) : SatisfiesM (fun r => r % 2 = k % 2) (addRandomEvens n k) := by
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
  satisfying (addRandomEvens_spec n k)

def program (n : Nat) (k : Nat) : IO Nat := do
  let r₁ ← addRandomEvens n k
  let r₂ ← addRandomEvens n k
  return r₁ + r₂

/-- Since we're adding even numbers to our number twice, and summing,
the entire result is even. -/
theorem program_spec (n k) : SatisfiesM (fun r => r % 2 = 0) (program n k) := by
  -- unfold program
  rw [program]
  -- apply the spec for addRandomEvens
  obtain ⟨r₁, h₁⟩ := addRandomEvens_spec n k
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
