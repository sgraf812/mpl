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

inductive PredShape : Type 1 where
  | pure : PredShape
  | arg : (σ : Type) → PredShape → PredShape
  | except : (ε : Type) → PredShape → PredShape

@[reducible]
def PreCond : PredShape → Type
  | .pure => Prop
  | .arg σ s => σ → PreCond s
  | .except _ s => PreCond s

@[reducible]
def FailConds : PredShape → Type
  | .pure => Unit
  | .arg _ s => FailConds s
  | .except ε s => (ε → PreCond s) × FailConds s

-- Translate a predicate shape to a multi-barreled postcondition
@[reducible]
def PostCond (α : Type) (s : PredShape) : Type :=
  (α → PreCond s) × FailConds s

open PredShape in
example {ρ ε σ : Type} : PreCond (arg σ (arg ρ (except ε pure))) = (σ → ρ → Prop) := rfl

section PostCondExamples
open PredShape

variable (α ρ ε ε₁ ε₂ σ σ₁ σ₂ : Type)
#reduce (types:=true) PreCond (except ε₂ (arg σ₂ (except ε₁ (arg σ₁ pure))))
#reduce (types:=true) PostCond α (except ε₂ (arg σ₂ (except ε₁ (arg σ₁ pure))))
-- at one point I also had PredShape.reader, but it's simpler to implement it as state
-- because then we can turn a precondition into a postcondition without complicated traversals.
-- Same for writer (presumably).
example : PostCond α (arg ρ pure) = ((α → ρ → Prop) × Unit) := rfl
example : PostCond α (except ε pure) = ((α → Prop) × (ε → Prop) × Unit) := rfl
example : PostCond α (arg σ (except ε pure)) = ((α → σ → Prop) × (ε → Prop) × Unit) := rfl
example : PostCond α (except ε (arg σ₁ pure)) = ((α → σ₁ → Prop) × (ε → σ₁ → Prop) × Unit) := rfl
example : PostCond α (arg σ₂ (except ε (arg σ₁ pure))) = ((α → σ₂ → σ₁ → Prop) × (ε → σ₁ → Prop) × Unit) := rfl
example : PostCond α (except ε₂ (arg σ₂ (except ε₁ (arg σ₁ pure)))) = ((α → σ₂ → σ₁ → Prop) × (ε₂ → σ₂ → σ₁ → Prop) × (ε₁ → σ₁ → Prop) × Unit) := rfl

-- #reduce (types := true) ((do pure ((← MonadReaderOf.read) < 13 ∧ (← MonadReaderOf.read) = "hi")) : PreCond (state Nat (state String pure)) Prop)

end PostCondExamples

-- instance PreCond.instMonad : {ps : PredShape} → Monad (PreCond ps)
--   | .pure => (inferInstance : Monad Id)
--   | .arg σ s => let _ := @instMonad s; (inferInstance : Monad (ReaderT σ (PreCond s)))
--   | .except ε s => @instMonad s

@[reducible]
def PreCond.pure : {ps : PredShape} → Prop → PreCond ps
  | .pure => fun p => p
  | .arg σ s => fun p (_s : σ) => @PreCond.pure s p
  | .except _ s => @PreCond.pure s

@[simp]
theorem PreCond.pure_except : @PreCond.pure (.except ε ps) p = (@PreCond.pure ps p : PreCond (.except ε ps)) := by
  rfl

@[simp]
theorem PreCond.pure_arg_apply {ps} {σ} {s:σ} :
  @PreCond.pure (.arg σ ps) p s = @PreCond.pure ps p := rfl

@[simp]
theorem PreCond.pure_pure : @PreCond.pure .pure p = p := rfl

noncomputable instance PreCond.instLattice : {ps : PredShape} → CompleteLattice (PreCond ps)
  | .pure => ((inferInstance : CompleteLattice Prop) : CompleteLattice (PreCond .pure))
  | .arg σ s => let _ := @instLattice s; (inferInstance : CompleteLattice (σ → PreCond s))
  | .except ε s => @instLattice s

noncomputable instance PreCond.instPreorder {ps : PredShape} : Preorder (PreCond ps) := inferInstance
noncomputable instance PreCond.instLE {ps : PredShape} : LE (PreCond ps) := inferInstance

theorem PreCond.imp_pure_extract {ps} {P : Prop} {P' : PreCond ps} {Q : PreCond ps}
  (h : P → P' ≤ Q) : PreCond.pure P ⊓ P' ≤ Q := by
  induction ps
  case pure => simp; exact h
  case arg σ s ih => intro s; apply ih (fun hp => h hp s)
  case except ε s ih => simp; apply ih h

def FailConds.const (p : Prop) : FailConds ps :=
  match ps with
  | .pure => ()
  | .arg σ s => @FailConds.const s p
  | .except ε s => (fun _ε => PreCond.pure p, @FailConds.const s p)

def FailConds.true : FailConds ps := FailConds.const True
def FailConds.false : FailConds ps := FailConds.const False

noncomputable instance FailConds.instPreorder : {ps : PredShape} → Preorder (FailConds ps)
  | .pure => inferInstance
  | .arg _ s => let _ := @instPreorder s; inferInstance
  | .except _ s => let _ := @instPreorder s; inferInstance

-- instance FailConds.instLE {ps : PredShape} : LE (FailConds ps) := FailConds.instPreorder.toLE

noncomputable instance PostCond.instPreorder : {ps : PredShape} → Preorder (PostCond α ps) := inferInstance
noncomputable instance PostCond.instLE {ps : PredShape} : LE (PostCond α ps) := inferInstance

@[simp]
lemma PreCond.bot_le {x : PreCond ps} : pure False ≤ x := by
  induction ps
  case pure => exact False.elim
  case arg σ s ih => intro; exact ih
  case except ε s ih => exact ih

@[simp]
lemma PreCond.le_top {x : PreCond ps} : x ≤ pure True := by
  induction ps
  case pure => exact fun _ => True.intro
  case arg σ s ih => intro; exact ih
  case except ε s ih => exact ih

@[simp]
lemma PreCond.glb_apply {x y : PreCond (.arg σ ps)} {s : σ} : (x ⊓ y) s = x s ⊓ y s := by
  rfl

@[simp]
lemma PreCond.lub_apply {x y : PreCond (.arg σ ps)} {s : σ} : (x ⊔ y) s = x s ⊔ y s := by
  rfl

@[simp]
lemma FailConds.bot_le {x : FailConds ps} : FailConds.false ≤ x := by
  simp only [false]
  induction ps
  case pure => simp
  case arg σ s ih => exact ih
  case except ε s ih => simp only [const, Prod.le_def, ih, and_true]; intro ε; exact PreCond.bot_le

@[simp]
lemma FailConds.le_top {x : FailConds ps} : x ≤ FailConds.true := by
  simp only [true]
  induction ps
  case pure => simp
  case arg σ s ih => exact ih
  case except ε s ih => simp only [const, Prod.le_def, ih, and_true]; intro ε; exact PreCond.le_top

-- A postcondition expressing total correctness
abbrev PostCond.total (p : α → PreCond ps) : PostCond α ps :=
  (p, FailConds.false)

-- A postcondition expressing partial correctness
abbrev PostCond.partial (p : α → PreCond ps) : PostCond α ps :=
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
lemma PostCond.total_def {p : α → PreCond ps} : (p, FailConds.false) = PostCond.total p := rfl
@[simp]
lemma PostCond.partial_def {p : α → PreCond ps} : (p, FailConds.true) = PostCond.partial p := rfl

@[simp]
lemma PostCond.le_total (p : α → PreCond ps) (q : PostCond α ps) : PostCond.total p ≤ q ↔ ∀ a, p a ≤ q.1 a := by
  simp only [total, Prod.le_def, le_refl, and_true, iff_true_intro FailConds.bot_le]
  rfl

@[simp]
lemma PostCond.le_partial (p q : α → PreCond ps) : PostCond.partial p ≤ PostCond.partial q ↔ ∀ a, p a ≤ q a := by
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

@[reducible]
def RelPreCond (ps : PredShape) : Type := PreCond ps → Prop

@[reducible]
def RelFailConds : PredShape → Type
  | .pure => Unit
  | .arg _ s => RelFailConds s
  | .except ε s => ((ε → PreCond s) → Prop) × RelFailConds s

-- Translate a predicate shape to a multi-barreled postcondition
@[reducible]
def RelPostCond (α : Type) (s : PredShape) : Type :=
  ((α → PreCond s) → Prop) × RelFailConds s

class WP (m : Type → Type) (ps : outParam PredShape) where
  wp (x : m α) (Q : PostCond α ps) : PreCond ps
open WP

instance Idd.instWP : WP Idd .pure where
  wp x Q := Q.1 x.run

instance StateT.instWP [Monad m] [WP m ps] : WP (StateT σ m) (.arg σ ps) where
  wp x Q := fun s => wp (x s) (fun (a, s') => Q.1 a s', Q.2)

instance ReaderT.instWP [Monad m] [WP m ps] : WP (ReaderT ρ m) (.arg ρ ps) where
  wp x Q := fun r => wp (x r) (fun a => Q.1 a r, Q.2)

instance ExceptT.instWP [Monad m] [WP m ps] : WP (ExceptT ε m) (.except ε ps) where
  wp x Q := wp (m:=m) x.run (fun | .ok a => Q.1 a | .error e => Q.2.1 e, Q.2.2)

instance EStateM.instWP : WP (EStateM ε σ) (.except ε (.arg σ .pure)) where
  wp x Q := fun s => match x s with
    | .ok a s' => Q.1 a s'
    | .error e s' => Q.2.1 e s'

class LawfulWP (m : Type → Type) (ps : outParam PredShape) [Monad m] [WP m ps] where
  wp_pure {α} (a : α) (Q : PostCond α ps) :
    Q.1 a ≤ wp (m:=m) (pure a) Q
  wp_bind {α β} (x : m α) (f : α → m β) {Q : PostCond β ps} :
    wp x (fun a => wp (f a) Q, Q.2) ≤ wp (x >>= f) Q
  wp_conseq {α} (x : m α) (Q₁ Q₂ : PostCond α ps) :
    Q₁ ≤ Q₂ → wp x Q₁ ≤ wp x Q₂

def LawfulWP.wp_pure_imp {m : Type → Type} [Monad m] [WP m ps] [LawfulWP m ps] {α} {P : PreCond ps} {Q : PostCond α ps} (a : α)
    (himp : P ≤ Q.1 a) : P ≤ wp (m:=m) (pure a) Q := le_trans himp (wp_pure a Q)

def LawfulWP.wp_bind_imp {m : Type → Type} [Monad m] [WP m ps] [LawfulWP m ps] {α β} {P : PostCond α ps} {Q : PostCond β ps} (x : m α) (f : α → m β)
    (hf : ∀a, P.1 a ≤ wp (f a) Q) (herror : P.2 ≤ Q.2) :
    wp x P ≤ wp (x >>= f) Q := le_trans (wp_conseq x P (fun a => wp (f a) Q, Q.2) ⟨hf, herror⟩) (wp_bind x f)

def LawfulWP.wp_conseq_2 {m : Type → Type} [Monad m] [WP m ps] [LawfulWP m ps] {α} (x : m α) (Q₁ Q₂ : PostCond α ps)
    (h1 : Q₁.1 ≤ Q₂.1) (h2 : Q₁.2 ≤ Q₂.2) :
    wp x Q₁ ≤ wp x Q₂ := wp_conseq x _ _ ⟨h1,h2⟩

open LawfulWP

instance Idd.instLawfulWP : LawfulWP Idd .pure where
  wp_pure a Q := by simp only [wp, Pure.pure, pure, le_refl]
  wp_bind x f Q := by simp only [wp, Bind.bind, bind, le_refl]
  wp_conseq x _ _ h := h.1 x.run

instance StateT.instLawfulWP [Monad m] [WP m ps] [LawfulWP m ps] : LawfulWP (StateT σ m) (.arg σ ps) where
  wp_pure a Q := by intro s; apply wp_pure (Q := (fun x => Q.1 x.1 x.2, Q.2)) (a,s)
  wp_bind x f Q := by intro s; apply wp_bind
  wp_conseq {α} x Q₁ Q₂ h := by
    intro s
    simp only [wp]
    apply wp_conseq (x s)
    simp only [Prod.mk_le_mk, h.2, and_true]
    intro x
    apply h.1

instance ReaderT.instLawfulWP [Monad m] [WP m ps] [LawfulWP m ps] : LawfulWP (ReaderT ρ m) (.arg ρ ps) where
  wp_pure a Q := by intro r; apply wp_pure_imp; simp
  wp_bind x f Q := by intro r; apply wp_bind
  wp_conseq {α} x Q₁ Q₂ h := by
    intro r
    apply wp_conseq (x r)
    simp only [Prod.mk_le_mk, h.2, and_true]
    intro x
    apply h.1

instance ExceptT.instLawfulWP [Monad m] [WP m ps] [LawfulWP m ps] : LawfulWP (ExceptT ε m) (.except ε ps) where
  wp_pure a Q := by apply wp_pure_imp (m:=m); simp
  wp_bind x f Q := by
    apply wp_bind_imp (m:=m) _ _ ?_ (by simp)
    intro b
    cases b
    case error a => apply wp_pure_imp (m:=m); simp
    case ok a => simp; apply wp_conseq (m:=m); simp
  wp_conseq x Q₁ Q₂ h := by
    simp [wp, bind, ExceptT.bind]
    apply wp_conseq _ _ _ ?_
    simp[h.2.2]
    intro x
    cases x
    case error e => apply h.2.1 e
    case ok a => apply h.1 a

instance EStateM.instLawfulWP : LawfulWP (EStateM ε σ) (.except ε (.arg σ .pure)) where
  wp_pure a Q := by simp [wp, Pure.pure, EStateM.pure]
  wp_bind x f Q := by
    intro s
    simp [wp, Bind.bind, EStateM.bind]
    cases (x s) <;> simp
  wp_conseq x Q₁ Q₂ h := by
    intro s
    simp[wp]
    cases (x s) <;> apply_rules [h.1,h.2.1]

def MonadTriple.triple {m : Type → Type} [WP m ps] {α} (x : m α) (P : PreCond ps) (Q : PostCond α ps) : Prop :=
  P ≤ wp x Q

open MonadTriple (triple)

theorem LawfulMonadTriple.triple_conseq {m : Type → Type} [Monad m] [WP m ps] [LawfulWP m ps] {α} (x : m α) {P P' : PreCond ps} {Q Q' : PostCond α ps}
  (hp : P ≤ P' := by simp) (hq : Q' ≤ Q := by simp) (h : triple x P' Q') :
  triple x P Q := by
    apply le_trans hp
    apply le_trans h
    apply wp_conseq x Q' Q hq

theorem LawfulMonadTriple.triple_extract_persistent {m : Type → Type} [Monad m] [WP m ps] [LawfulWP m ps] {P : Prop} {P' : PreCond ps} {Q : PostCond α ps}
  (x : m α) (h : P → triple x P' Q) :
  triple x (PreCond.pure P ⊓ P') Q := PreCond.imp_pure_extract h

theorem LawfulMonadTriple.triple_pure {m : Type → Type} [Monad m] [WP m ps] [LawfulWP m ps] {α} {Q : PostCond α ps} (a : α) (himp : P ≤ Q.1 a) :
  triple (pure (f:=m) a) P Q := wp_pure_imp _ himp

theorem LawfulMonadTriple.triple_bind {m : Type → Type} [Monad m] [WP m ps] [LawfulWP m ps] {α β} {P : PreCond ps} {Q : α → PreCond ps} {R : PostCond β ps} (x : m α) (f : α → m β)
  (hx : triple x P (Q, R.2))
  (hf : ∀ b, triple (f b) (Q b) R) :
  triple (x >>= f) P R := by
    apply le_trans hx
    apply wp_bind_imp _ _ hf (by simp)

theorem LawfulMonadTriple.triple_conseq_l {m : Type → Type} [Monad m] [WP m ps] [LawfulWP m ps] {P P' : PreCond ps} {Q : PostCond α ps}
  (x : m α) (hp : P ≤ P') (h : triple x P' Q) :
  triple x P Q := triple_conseq x hp le_rfl h

theorem LawfulMonadTriple.triple_conseq_r {m : Type → Type} [Monad m] [WP m ps] [LawfulWP m ps] {P : PreCond ps} {Q Q' : PostCond α ps}
  (x : m α) (hq : Q ≤ Q') (h : triple x P Q) :
  triple x P Q' := triple_conseq x le_rfl hq h

theorem LawfulMonadTriple.triple_map {m : Type → Type} [Monad m] [LawfulMonad m] [WP m ps] [LawfulWP m ps] (f : α → β) (x : m α)
  (h : triple x P (fun a => Q.1 (f a), Q.2)) :
  triple (f <$> x) P Q := by
    simp only [← bind_pure_comp]
    apply triple_bind _ _ h
    intro b
    apply triple_pure
    simp only [le_refl]

theorem LawfulMonadTriple.triple_seq {m : Type → Type} [Monad m] [LawfulMonad m] [WP m ps] [LawfulWP m ps] (f : m (α → β)) (x : m α) {Q : (α → β) → PreCond ps}
  (hf : triple f P (Q, R.2))
  (hx : ∀ f, triple x (Q f) (fun a => R.1 (f a), R.2)) :
  triple (f <*> x) P R := by
    simp only [← bind_map]
    apply triple_bind _ _ hf ?_
    intro f
    apply triple_map _ _ (hx f)

theorem LawfulMonadTriple.triple_extract_persistent_true {m : Type → Type} [Monad m] [LawfulMonad m] [WP m ps] [LawfulWP m ps] {P : Prop} {Q : PostCond α ps}
  (x : m α) (h : P → triple x (PreCond.pure True) Q) :
  triple x (PreCond.pure P) Q := by
    have : PreCond.pure P = (PreCond.pure P ⊓ PreCond.pure True : PreCond ps) := by simp
    rw[this]
    exact triple_extract_persistent x h

theorem LawfulMonadTriple.triple_dite {c : Prop} [Decidable c] {t : c → m α} {e : ¬c → m α} {P : PreCond ps} {Q : PostCond α ps} [Monad m] [WP m ps]
  (htrue : (h : c) → triple (t h) P Q)
  (hfalse : (h : ¬c) → triple (e h) P Q) :
  triple (dite c t e) P Q := by
    split <;> simp only [htrue, hfalse]

theorem LawfulMonadTriple.triple_ite {c : Prop} [Decidable c] {t : m α} {e : m α} {P : PreCond ps} {Q : PostCond α ps} [Monad m] [WP m ps]
  (htrue : c → triple t P Q)
  (hfalse : ¬c → triple e P Q) :
  triple (ite c t e) P Q := by
    change triple (dite c (fun _ => t) (fun _ => e)) P Q
    exact triple_dite htrue hfalse

open LawfulMonadTriple

structure LiftPredImpl (m : PredShape) (n : PredShape) where
  lift_pre : PreCond m → PreCond n
  lift_fail_conds : FailConds m → FailConds n

def LiftPredImpl.lift_post {m n : PredShape} (impl : LiftPredImpl m n) (Q : PostCond α m) : PostCond α n :=
  (fun a => impl.lift_pre (Q.1 a), impl.lift_fail_conds Q.2)

def LiftPredImpl.compose {m n o : PredShape} (impl₂ : LiftPredImpl n o) (impl₁ : LiftPredImpl m n) : LiftPredImpl m o :=
  ⟨impl₂.lift_pre ∘ impl₁.lift_pre, impl₂.lift_fail_conds ∘ impl₁.lift_fail_conds⟩

@[simp]
theorem LiftPredImpl.compose_lift_pre {m n o : PredShape} (impl₂ : LiftPredImpl n o) (impl₁ : LiftPredImpl m n) :
  (compose impl₂ impl₁).lift_pre = impl₂.lift_pre ∘ impl₁.lift_pre := rfl

@[simp]
theorem LiftPredImpl.compose_lift_fail_conds {m n o : PredShape} (impl₂ : LiftPredImpl n o) (impl₁ : LiftPredImpl m n) :
  (compose impl₂ impl₁).lift_fail_conds = impl₂.lift_fail_conds ∘ impl₁.lift_fail_conds := rfl

@[simp]
theorem LiftPredImpl.compose_lift_post {m n o : PredShape} {α : Type} (impl₂ : LiftPredImpl n o) (impl₁ : LiftPredImpl m n) :
  (compose impl₂ impl₁).lift_post (α := α) = impl₂.lift_post ∘ impl₁.lift_post := rfl

class LawfulMonadLiftTriple (m : semiOutParam (Type → Type)) (n : Type → Type) (psm : outParam PredShape) (psn : outParam PredShape)
  [MonadLift m n] [WP m psm] [WP n psn] where
  lift_pred_impl : LiftPredImpl psm psn
  triple_lift {x : m α} {P : PreCond psm} {Q : PostCond α psm}
    (h : triple x P Q) :
    triple (m:=n) (liftM x) (lift_pred_impl.lift_pre P) (lift_pred_impl.lift_post Q)

class LawfulMonadLiftTripleT (m : Type → Type) (n : Type → Type) (psm : outParam PredShape) (psn : outParam PredShape)
  [MonadLiftT m n] [WP m psm] [WP n psn] where
  lift_pred_impl : LiftPredImpl psm psn
  triple_lift {x : m α} {P : PreCond psm} {Q : PostCond α psm}
    (h : triple x P Q) :
    triple (m:=n) (liftM x) (lift_pred_impl.lift_pre P) (lift_pred_impl.lift_post Q)

def LawfulMonadLiftTripleT.triple_lift_r [Monad n] [MonadLiftT m n] [WP m psm] [WP n psn] [LawfulWP n psn] [inst : LawfulMonadLiftTripleT m n psm psn] {x : m α} {P : PreCond psm} {Q : PostCond α psm} {Q' : PostCond α psn}
  (h : triple x P Q) (h' : inst.lift_pred_impl.lift_post Q ≤ Q') :
  triple (m:=n) (liftM x) (inst.lift_pred_impl.lift_pre P) Q' := triple_conseq_r _ h' (inst.triple_lift h)

def LawfulMonadLiftTripleT.triple_lift_l [Monad n] [MonadLiftT m n] [WP m psm] [WP n psn] [LawfulWP n psn] [inst : LawfulMonadLiftTripleT m n psm psn] {x : m α} {P' : PreCond psn} {P : PreCond psm}
  (h : triple x P Q) (h' : P' ≤ inst.lift_pred_impl.lift_pre P) :
  triple (m:=n) (liftM x) P' (inst.lift_pred_impl.lift_post Q) := triple_conseq_l _ h' (inst.triple_lift h)

def LawfulMonadLiftTripleT.triple_lift_conseq [Monad n] [MonadLiftT m n] [WP m psm] [WP n psn] [LawfulWP n psn] [inst : LawfulMonadLiftTripleT m n psm psn] {x : m α} {P : PreCond psm} {Q : PostCond α psm} {P' : PreCond psn} {Q' : PostCond α psn}
  (hp : P' ≤ inst.lift_pred_impl.lift_pre P) (hq : inst.lift_pred_impl.lift_post Q ≤ Q') (h : triple x P Q) :
  triple (m:=n) (liftM x) P' Q' := triple_conseq _ hp hq (inst.triple_lift h)

open LawfulMonadLiftTripleT (triple_lift triple_lift_r triple_lift_l)

instance (m n o) [WP m psm] [WP n psn] [WP o pso]
  [MonadLift n o] [inst1 : LawfulMonadLiftTriple n o psn pso]
  [MonadLiftT m n] [instT : LawfulMonadLiftTripleT m n psm psn] : LawfulMonadLiftTripleT m o psm pso where
  lift_pred_impl := LiftPredImpl.compose inst1.lift_pred_impl instT.lift_pred_impl
  triple_lift h := by
    simp only [liftM, monadLift, LiftPredImpl.compose_lift_pre, Function.comp_apply,
      LiftPredImpl.compose_lift_post]
    apply LawfulMonadLiftTriple.triple_lift
    apply LawfulMonadLiftTripleT.triple_lift
    assumption

instance (m) [WP m psm] : LawfulMonadLiftTripleT m m psm psm where
  lift_pred_impl :=
  { lift_pre P := P
    lift_fail_conds fc := fc }
  triple_lift h := h

instance StateT.instLawfulMonadLiftTriple [Monad m][WP m ps] [LawfulWP m ps] :
  LawfulMonadLiftTriple m (StateT σ m) ps (.arg σ ps) where
  lift_pred_impl :=
  { lift_pre P := fun _s => P
    lift_fail_conds fc := fc }
  triple_lift h := by
    simp only [triple, liftM, monadLift, MonadLift.monadLift, StateT.lift, LiftPredImpl.lift_post]
    intros
    apply LawfulMonadTriple.triple_bind _ _
    case hx => exact h
    case hf => simp[LawfulWP.triple_pure]

@[simp]
theorem LawfulMonadLiftTriple.StateT.lift_pre_def [Monad m] [WP m ps] [LawfulMonad m] [LawfulWP m ps] :
  (LawfulMonadLiftTriple.lift_pred_impl m (StateT σ m)).lift_pre P s = P := rfl

@[simp]
theorem LawfulMonadLiftTriple.StateT.lift_fail_conds_def [Monad m] [WP m ps] [LawfulMonad m] [LawfulWP m ps] :
  (LawfulMonadLiftTriple.lift_pred_impl m (StateT σ m)).lift_fail_conds fc = fc := rfl

@[simp]
theorem LawfulMonadLiftTriple.StateT.lift_post_def [Monad m] [WP m ps] [LawfulMonad m] [LawfulWP m ps] :
  (LawfulMonadLiftTriple.lift_pred_impl m (StateT σ m)).lift_post Q = (fun a _ => Q.1 a, Q.2) := rfl

@[simp]
theorem LawfulMonadLiftTripleT.StateT.lift_pre_def [Monad m] [WP m ps] [LawfulMonad m] [LawfulWP m ps] :
  (LawfulMonadLiftTripleT.lift_pred_impl m (StateT σ m)).lift_pre P s = P := rfl

@[simp]
theorem LawfulMonadLiftTripleT.StateT.lift_fail_conds_def [Monad m] [WP m ps] [LawfulMonad m] [LawfulWP m ps] :
  (LawfulMonadLiftTripleT.lift_pred_impl m (StateT σ m)).lift_fail_conds fc = fc := rfl

@[simp]
theorem LawfulMonadLiftTripleT.StateT.lift_post_def [Monad m] [WP m ps] [LawfulMonad m] [LawfulWP m ps] :
  (LawfulMonadLiftTripleT.lift_pred_impl m (StateT σ m)).lift_post Q = (fun a _ => Q.1 a, Q.2) := rfl

instance ReaderT.instLawfulMonadLiftTriple [Monad m] [WP m ps] :
  LawfulMonadLiftTriple m (ReaderT ρ m) ps (.arg ρ ps) where
  lift_pred_impl :=
  { lift_pre P := fun _r => P
    lift_fail_conds fc := fc }
  triple_lift h := by
    simp only [triple, liftM, monadLift, MonadLift.monadLift, LiftPredImpl.lift_post]
    intros
    apply h

@[simp]
theorem LawfulMonadLiftTriple.ReaderT.lift_pre_def [Monad m] [WP m ps] :
  (LawfulMonadLiftTriple.lift_pred_impl m (ReaderT ρ m)).lift_pre P s = P := rfl

@[simp]
theorem LawfulMonadLiftTriple.ReaderT.lift_fail_conds_def [Monad m] [WP m ps] :
  (LawfulMonadLiftTriple.lift_pred_impl m (ReaderT ρ m)).lift_fail_conds fc = fc := rfl

@[simp]
theorem LawfulMonadLiftTriple.ReaderT.lift_post_def [Monad m] [WP m ps] :
  (LawfulMonadLiftTriple.lift_pred_impl m (ReaderT ρ m)).lift_post Q = (fun a _ => Q.1 a, Q.2) := rfl

@[simp]
theorem LawfulMonadLiftTripleT.ReaderT.lift_pre_def [Monad m] [WP m ps] :
  (LawfulMonadLiftTripleT.lift_pred_impl m (ReaderT ρ m)).lift_pre P s = P := rfl

@[simp]
theorem LawfulMonadLiftTripleT.ReaderT.lift_fail_conds_def [Monad m] [WP m ps] :
  (LawfulMonadLiftTripleT.lift_pred_impl m (ReaderT ρ m)).lift_fail_conds fc = fc := rfl

@[simp]
theorem LawfulMonadLiftTripleT.ReaderT.lift_post_def [Monad m] [WP m ps] :
  (LawfulMonadLiftTripleT.lift_pred_impl m (ReaderT ρ m)).lift_post Q = (fun a _ => Q.1 a, Q.2) := rfl

instance ExceptT.instLawfulMonadLiftTriple [Monad m] [LawfulMonad m] [WP m ps] [LawfulWP m ps] :
  LawfulMonadLiftTriple m (ExceptT ε m) ps (.except ε ps) where
  lift_pred_impl :=
  { lift_pre P := P
    lift_fail_conds fc := (fun _e => PreCond.pure False, fc) }
  triple_lift h := by
    simp only [triple, liftM, monadLift, MonadLift.monadLift, run_lift, LiftPredImpl.lift_post]
    apply triple_map
    apply h

@[simp]
theorem LawfulMonadLiftTriple.ExceptT.lift_pre_def [Monad m] [WP m ps] [LawfulMonad m] [LawfulWP m ps] :
  (LawfulMonadLiftTriple.lift_pred_impl m (ExceptT ε m)).lift_pre P = P := rfl

@[simp]
theorem LawfulMonadLiftTriple.ExceptT.lift_fail_conds_def [Monad m] [WP m ps] [LawfulMonad m] [LawfulWP m ps] :
  (LawfulMonadLiftTriple.lift_pred_impl m (ExceptT ε m)).lift_fail_conds fc = (fun _e => PreCond.pure False, fc) := rfl

@[simp]
theorem LawfulMonadLiftTriple.ExceptT.lift_post_def [Monad m] [WP m ps] [LawfulMonad m] [LawfulWP m ps] :
  (LawfulMonadLiftTriple.lift_pred_impl m (ExceptT ε m)).lift_post Q = (fun a => Q.1 a, (fun _e => PreCond.pure False, Q.2)) := rfl

@[simp]
theorem LawfulMonadLiftTripleT.ExceptT.lift_pre_def [Monad m] [WP m ps] [LawfulMonad m] [LawfulWP m ps] :
  (LawfulMonadLiftTripleT.lift_pred_impl m (ExceptT ε m)).lift_pre P = P := rfl

@[simp]
theorem LawfulMonadLiftTripleT.ExceptT.lift_fail_conds_def [Monad m] [WP m ps] [LawfulMonad m] [LawfulWP m ps] :
  (LawfulMonadLiftTripleT.lift_pred_impl m (ExceptT ε m)).lift_fail_conds fc = (fun _e => PreCond.pure False, fc) := rfl

@[simp]
theorem LawfulMonadLiftTripleT.ExceptT.lift_post_def [Monad m] [WP m ps] [LawfulMonad m] [LawfulWP m ps] :
  (LawfulMonadLiftTripleT.lift_pred_impl m (ExceptT ε m)).lift_post Q = (fun a => Q.1 a, (fun _e => PreCond.pure False, Q.2)) := rfl

notation:lead "⦃" P "⦄ " x:lead " ⦃" Q "⦄" =>
  MonadTriple.triple x P Q
notation:lead "⦃" P "⦄ " x:lead " ⦃⇓" v " | " Q "⦄" =>
  ⦃P⦄ x ⦃PostCond.total fun v => Q⦄

theorem Triple.forIn_list {α β} {m : Type → Type}
  [Monad m] [LawfulMonad m] [WP m ps] [LawfulWP m ps]
  {xs : List α} {init : β} {f : α → β → m (ForInStep β)}
  (inv : PostCond (List α × β) ps)
  (hpre : P ≤ inv.1 (xs, init))
  (hstep : ∀ hd tl b,
      ⦃inv.1 (hd :: tl, b)⦄
      (f hd b)
      ⦃(fun r => match r with | .yield b' => inv.1 (tl, b') | .done b' => inv.1 ([], b'), inv.2)⦄) :
  ⦃P⦄ (forIn xs init f) ⦃(fun b' => inv.1 ([], b'), inv.2)⦄ := by
    apply triple_conseq _ hpre le_rfl
    clear hpre
    induction xs generalizing init
    case nil => apply LawfulMonadTriple.triple_pure; simp
    case cons hd tl ih =>
      simp only [List.forIn_cons]
      apply LawfulMonadTriple.triple_bind
      case hx => exact hstep hd tl init
      case hf =>
        intro b
        split
        · apply LawfulMonadTriple.triple_pure; simp
        · exact ih

theorem Triple.foldlM_list {α β} {m : Type → Type}
  [Monad m] [LawfulMonad m] [WP m ps] [LawfulWP m ps]
  {xs : List α} {init : β} {f : β → α → m β}
  (inv : PostCond (List α × β) ps)
  (hpre : P ≤ inv.1 (xs, init))
  (hstep : ∀ hd tl b,
      ⦃inv.1 (hd :: tl, b)⦄
      (f b hd)
      ⦃(fun b' => inv.1 (tl, b'), inv.2)⦄) :
  ⦃P⦄ (List.foldlM f init xs) ⦃(fun b' => inv.1 ([], b'), inv.2)⦄ := by
  have : xs.foldlM f init = forIn xs init (fun a b => .yield <$> f b a) := by
    simp only [List.forIn_yield_eq_foldlM, id_map']
  rw[this]
  apply Triple.forIn_list inv hpre
  intro hd tl b
  apply LawfulMonadTriple.triple_map ForInStep.yield _ (hstep hd tl b)

end Triple

section IO

axiom IO.wp {α ε} (x : EIO ε α) (p : Except ε α → Prop) : Prop
axiom IO.wp_conseq {α ε} {x : EIO ε α} {Q Q' : Except ε α → Prop} :
  Q ≤ Q' → IO.wp x Q → IO.wp x Q'
axiom IO.wp_pure {α ε} {Q : Except ε α → Prop} (a : α) (h : Q (.ok a)) :
  IO.wp (pure a) Q
axiom IO.wp_bind {α β ε} {Q : Except ε β → Prop} {x : EIO ε α} {f : α → EIO ε β}
  (hx : IO.wp x (fun | .ok a => wp (f a) Q | .error e => Q (.error e))) :
  IO.wp (x >>= f) Q

instance IO.instWP : WP (EIO ε) (.except ε .pure) where
  wp x Q := IO.wp x (fun | .ok a => Q.1 a | .error e => Q.2.1 e)

instance IO.instLawfulWP : LawfulWP (EIO ε) (.except ε .pure) where
  wp_conseq x _ _ h := by
    apply IO.wp_conseq
    intro x
    cases x <;> apply_rules [h.1, h.2.1]
  wp_pure x h := by intro hp; apply IO.wp_pure x hp
  wp_bind x f Q := by
    intro hx
    apply IO.wp_bind
    apply wp_conseq _ hx
    intro x
    simp only [WP.wp]
    cases x <;> simp

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

theorem test_3 : ⦃True⦄ (do let mut x := 0; for i in [1:5] do { x := x + i }; pure (f := Idd) (); return x) ⦃⇓r | r < 30⦄ := by
  open LawfulMonadTriple in
  simp
  apply triple_conseq_r _ ?hpost (Triple.forIn_list (m:=Idd) (PostCond.total fun (xs, r) => (∀ x, x ∈ xs → x ≤ 5) ∧ r + xs.length * 5 ≤ 25) ?hpre ?hstep)
  case hpre => intro xs; simp; omega
  case hpost => simp; intro; simp; omega
  case hstep => intros; apply triple_pure; simp_all; omega

theorem test_3_2 : ⦃True⦄ (do let mut x := 0; for i in [1:5] do { x := x + i }; pure (f := Idd) (); return x) ⦃⇓r | r = 10⦄ := by
  open LawfulMonadTriple in
  simp
  apply triple_conseq_r _ ?hpost (Triple.forIn_list (m:=Idd) (PostCond.total fun (xs, r) => r + xs.sum = 10) ?hpre ?hstep)
  case hpre => simp; rfl
  case hpost => simp
  case hstep => intros; apply triple_pure; simp_all; omega

-- TBD: Figure out while loops
theorem test_4 : ⦃True⦄ (do let mut x := 0; let mut i := 0; while i < 4 do { x := x + i; i := i + 1 }; pure (f := Idd) (); return x) ⦃⇓r | r = 6⦄ := by
  open LawfulMonadTriple in
  simp
  sorry

theorem test_1 : ⦃True⦄ (do let mut id := 5; id := 3; pure (f := Idd) id) ⦃⇓r | r = 3⦄ := by
  simp[LawfulMonadTriple.triple_pure]

theorem test_2 : ⦃True⦄ (do let mut x := 5; if x > 1 then { x := 1 } else { x := x }; pure (f:=Idd) x) ⦃⇓r | r = 1⦄ := by
  simp[LawfulMonadTriple.triple_pure]

theorem test_2_2 : ⦃True⦄ (do let mut id := 5; id := 3; pure (f := Idd) id) ⦃⇓r | r < 20⦄ := by
  simp[LawfulMonadTriple.triple_pure]

-- theorem StateT.get_spec2 [Monad m] [MonadState σ m] [WP m stack] [LawWP m] [LawfulMonadTriple m stack] {P : PreCond stack} :
--   ⦃LawfulMonadLiftTriple.lift_pred_impl.lift_pre P⦄
--   (get : m σ)
--   ⦃⇓r | do pure (P (← read) ⊓ P r)⦄ := by
--   simp [MonadTriple.triple, get, getThe, MonadStateOf.get, StateT.get, PostCond.total_fst, LawfulMonadTriple.triple_pure]

theorem StateT.get_spec [Monad m] [WP m stack] [LawfulWP m stack] {P : σ → PreCond stack} :
  ⦃P⦄
  (get : StateT σ m σ)
  ⦃⇓r | fun s => P s ⊓ P r⦄ := by
  simp [MonadTriple.triple, get, getThe, MonadStateOf.get, StateT.get, PostCond.total_fst, LawfulMonadTriple.triple_pure]

theorem StateT.get_spec' [Monad m] [WP m stack] [LawfulWP m stack] {P : σ → PreCond stack} :
  ⦃P⦄
  (get : StateT σ m σ)
  ⦃⇓r | fun s => PreCond.pure (s = r) ⊓ P r⦄ := by
  simp [MonadTriple.triple, get, getThe, MonadStateOf.get, StateT.get, PostCond.total_fst, LawfulMonadTriple.triple_pure]

theorem StateT.get_spec_bwd [Monad m] [WP m stack] [LawfulWP m stack] :
  ⦃fun s => Q.1 s s⦄
  (get : StateT σ m σ)
  ⦃Q⦄ := by
  simp [MonadTriple.triple, get, getThe, MonadStateOf.get, StateT.get, PostCond.total_fst, LawfulMonadTriple.triple_pure]

theorem StateT.get_spec_fwd [Monad m] [WP m stack] [LawfulMonad m] [LawfulWP m stack] {P : σ → PreCond stack} :
  ⦃P⦄ (get : StateT σ m σ) ⦃⇓r | fun s => PreCond.pure (s = r) ⊓ P r⦄ :=
  LawfulMonadTriple.triple_conseq_l get (by intro s; simp) (StateT.get_spec_bwd (m := m))

theorem StateT.set_spec_fwd [Monad m] [WP m stack] [LawfulMonad m] [LawfulWP m stack] {P : σ → PreCond stack} :
  ⦃P⦄ (set x : StateT σ m PUnit) ⦃⇓_ | fun s => PreCond.pure (s = x) ⊓ (⨆ s', P s')⦄ := by
  simp +contextual [MonadTriple.triple, set, StateT.set, LawfulMonadTriple.triple_pure, le_iSup_iff]

theorem StateT.set_spec_bwd [Monad m] [WP m stack] [LawfulMonad m] [LawfulWP m stack] :
  ⦃fun _ => Q.1 ⟨⟩ x⦄ (set x : StateT σ m PUnit) ⦃Q⦄ := by
  simp only [MonadTriple.triple, set, StateT.set, le_refl, LawfulMonadTriple.triple_pure, implies_true]

theorem StateT.set_spec_fwd_deriv [Monad m] [WP m stack] [LawfulMonad m] [LawfulWP m stack] {P : σ → PreCond stack} :
  ⦃P⦄ (set x : StateT σ m PUnit) ⦃⇓_ | fun s => PreCond.pure (s = x) ⊓ (⨆ s', P s')⦄ :=
  LawfulMonadTriple.triple_conseq_l _ (by intro; simp +contextual [le_iSup_iff]) (StateT.set_spec_bwd (m := m))

theorem StateT.set_spec_bwd_deriv [Monad m] [WP m stack] [LawfulMonad m] [LawfulWP m stack] {P : σ → PreCond stack} :
  ⦃fun _ => Q.1 ⟨⟩ x⦄ (set x : StateT σ m PUnit) ⦃Q⦄ :=
  LawfulMonadTriple.triple_conseq_r _ (by simp +contextual [le_iSup_iff]; intro ⟨⟩ s; simp +contextual [le_iSup_iff]) (StateT.set_spec_fwd (m := m))

theorem ExceptT.throw_spec [Monad m] [WP m stack] [LawfulWP m stack] {P : PreCond (.except ε stack)} :
  ⦃P⦄
  (throw e : ExceptT ε m σ)
  ⦃(fun _ => PreCond.pure False, fun e' => PreCond.pure (e = e') ⊓ P, FailConds.false)⦄ := by
  simp only [MonadTriple.triple, run_throw, PostCond.total_def, PreCond.le_top, inf_of_le_right,
    le_refl, LawfulMonadTriple.triple_pure]

theorem ExceptT.throw_spec_bwd [Monad m] [WP m stack] [LawfulWP m stack] :
  ⦃Q.2.1 e⦄
  (throw e : ExceptT ε m σ)
  ⦃Q⦄ := by
  simp only [MonadTriple.triple, run_throw, PostCond.total_def, PreCond.le_top, inf_of_le_right,
    le_refl, LawfulMonadTriple.triple_pure]

theorem test_ex :
  ⦃fun s => s = 4⦄
  (do let mut x := 0; let s ← get; for i in [1:s] do { x := x + i; if x > 4 then throw 42 }; pure (f := ExceptT Nat (StateT Nat Idd)) (); return x)
  ⦃(fun r s => False,
    fun e s => e = 42 ∧ s = 4,
    ())⦄ := by
  open LawfulMonadTriple in
  open LawfulMonadLiftTriple in
  simp
  apply triple_bind _ _ ?hx ?_
  case hx => exact triple_conseq_r _ (by simp; exact ⟨le_rfl, by intro e s; simp⟩) (triple_lift (StateT.get_spec (m := Idd)))
  intro s
  let inv : PostCond (List Nat × Nat) (.except Nat (.arg Nat .pure)) :=
    (fun (xs, r) s => r ≤ 4 ∧ s = 4 ∧ r + xs.sum > 4, fun e s => e = 42 ∧ s = 4, ())
  apply triple_conseq_r _ ?hpost (Triple.forIn_list (m:=ExceptT Nat (StateT Nat Idd)) inv ?hpre ?hstep)
  case hpre =>
    intro _ h
    simp[h,inv]
    conv in (List.sum _) => whnf
    simp
  case hpost =>
    simp only [List.sum_nil, add_zero, gt_iff_lt, Prod.mk_le_mk, le_refl, and_true, inv]
    intro r s
    simp_all
  case hstep =>
    intro hd tl x
    simp[inv]
    apply triple_dite
    case htrue =>
      intro h
      apply triple_conseq_r _ ?hpost (ExceptT.throw_spec (m := StateT Nat Idd) (P := fun s => x ≤ 4 ∧ s = 4 ∧ 4 < x + (hd + tl.sum)))
      simp only [Prod.mk_le_mk, le_refl, and_true, inv]
      constructor
      · intro; apply PreCond.bot_le
      · intro _ _; simp_all
    case hfalse =>
      intro h
      apply triple_pure
      intro s
      simp_all
      omega

theorem Triple.forIn_list_bwd {α β} {m : Type → Type}
  [Monad m] [LawfulMonad m] [WP m ps] [LawfulWP m ps]
  {xs : List α} {init : β} {f : α → β → m (ForInStep β)} {Q : PostCond β ps}
  (inv : PostCond (List α × β) ps)
  (hpost1 : ∀ b, inv.1 ([], b) ≤ Q.1 b)
  (hpost2 : inv.2 ≤ Q.2)
  (hstep : ∀ hd tl b,
      ⦃inv.1 (hd :: tl, b)⦄
      (f hd b)
      ⦃(fun r => match r with | .yield b' => inv.1 (tl, b') | .done b' => inv.1 ([], b'), inv.2)⦄) :
  ⦃inv.1 (xs, init)⦄ (forIn xs init f) ⦃Q⦄ := by
    let inv' := (fun b => inv.1 ([], b), inv.2)
    have hpost : inv' ≤ Q := ⟨hpost1, hpost2⟩
    apply LawfulMonadTriple.triple_conseq _ le_rfl hpost
    apply Triple.forIn_list inv le_rfl hstep

--theorem triple_lift_bwd {x : m α} {P : PreCond psm} {Q : PostCond α psm}
--    (h : triple x P Q) :
--    triple (m:=n) (liftM x) (lift_pred_impl.lift_pre P) (lift_pred_impl.lift_post Q)

theorem test_ex_bwd :
  ⦃fun s => s = 4⦄
  (do let mut x := 0; let s ← get; for i in [1:s] do { x := x + i; if x > 4 then throw 42 }; pure (f := ExceptT Nat (StateT Nat Idd)) (); return x)
  ⦃(fun r s => False,
    fun e s => e = 42 ∧ s = 4,
    ())⦄ := by
  open LawfulMonadTriple in
  open LawfulMonadLiftTriple in
  simp
  apply triple_bind _ _ ?later ?now
  case now =>
    intro s
    let inv : PostCond (List Nat × Nat) (.except Nat (.arg Nat .pure)) :=
        (fun (xs, r) s => r ≤ 4 ∧ s = 4 ∧ r + xs.sum > 4, fun e s => e = 42 ∧ s = 4, ())
    apply Triple.forIn_list_bwd (m:=ExceptT Nat (StateT Nat Idd)) inv ?hpost1 ?hpost2 ?hstep
    case hpost1 =>
      simp only [List.sum_nil, add_zero, gt_iff_lt, Prod.mk_le_mk, le_refl, and_true, inv]
      intro r s
      simp_all
    case hpost2 => simp[inv]
    case hstep =>
      intro hd tl x
      simp[inv]
      apply triple_dite
      case htrue =>
        intro h
        apply triple_conseq_l _ ?_ (ExceptT.throw_spec_bwd (m := StateT Nat Idd))
        intro s
        simp_all
      case hfalse =>
        intro h
        apply triple_pure
        intro s
        simp_all
        omega
  case later =>
    simp
    apply LawfulMonadLiftTripleT.triple_lift_conseq ?hpre ?hpost (StateT.get_spec_bwd (Q := (fun s s_1 => s_1 = 4 ∧ 4 < (List.range' 1 (s - 1) 1).sum, ())) (m := Idd))
    case hpre =>
      intro s h
      simp only [h, LawfulMonadLiftTripleT.ExceptT.lift_pre_def, Nat.add_one_sub_one, true_and]
      conv in (List.sum _) => whnf
      simp
    case hpost =>
      simp
      intro e
      simp
      exact PreCond.bot_le

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

axiom IO.rand_spec {n : Nat} : ⦃True⦄ (IO.rand 0 n : IO Nat) ⦃⇓r | r < n⦄

/-- The result has the same parity as the input. -/
theorem addRandomEvens_spec (n k) : ⦃True⦄ (addRandomEvens n k) ⦃⇓r | r % 2 = k % 2⦄ := by
  let _ := (PreCond.instPreorder : Preorder (PreCond (.except IO.Error .pure)))
  simp only [addRandomEvens, bind_pure_comp, map_pure, List.forIn_yield_eq_foldlM, bind_pure]
  apply LawfulMonadTriple.triple_conseq _ _ le_rfl (Triple.foldlM_list (m:=IO) (fun xs r => r % 2 = k % 2) ?step)
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
  simp

/-- Since we're adding even numbers to our number twice, and summing,
the entire result is even. -/
theorem program_spec (n k) : ⦃True⦄ program n k ⦃⇓r | r % 2 = 0⦄ := by
  let _ := (PreCond.instPreorder : Preorder (PreCond (.except IO.Error .pure)))
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
