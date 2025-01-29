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

attribute [vc_gen] Preorder.le_refl

section StateT

def StateT.le [base : ∀{α}, LE (w α)] : StateT σ w α → StateT σ w α → Prop :=
  fun x y => ∀s, x.run s ≤ y.run s
instance [base : ∀{α}, LE (w α)] : LE (StateT σ w α) := ⟨StateT.le⟩
instance [base : ∀{α}, Preorder (w α)] : Preorder (StateT σ w α) where
  __ := inferInstanceAs (LE (StateT σ w α))
  le_refl := fun x => fun s => le_refl (x.run s)
  le_trans := fun x y z hxy hyz => fun s => (hxy s).trans (hyz s)
instance [base : ∀{α}, PartialOrder (w α)] : PartialOrder (StateT σ w α) where
  __ := inferInstanceAs (Preorder (StateT σ w α))
  le_antisymm := fun _ _ hxy hyx => funext fun s => (hxy s).antisymm (hyx s)
instance [base : ∀{α}, SemilatticeSup (w α)] : SemilatticeSup (StateT σ w α) where
  __ := inferInstanceAs (PartialOrder (StateT σ w α))
instance [base : ∀{α}, SemilatticeInf (w α)] : SemilatticeInf (StateT σ w α) where
  __ := inferInstanceAs (PartialOrder (StateT σ w α))
instance [base : ∀{α}, Lattice (w α)] : Lattice (StateT σ w α) where
  __ := inferInstanceAs (SemilatticeSup (StateT σ w α))
  __ := inferInstanceAs (SemilatticeInf (StateT σ w α))
instance [base : ∀{α}, CompleteLattice (w α)] : CompleteLattice (StateT σ w α) where
  __ := inferInstanceAs (Lattice (StateT σ w α))

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
attribute [vc_gen] LawfulMonadState.get_set LawfulMonadState.set_get LawfulMonadState.set_set LawfulMonadState.set_get_pure
-- attribute [simp] LawfulMonadState.get_set LawfulMonadState.set_get LawfulMonadState.set_set LawfulMonadState.set_get_pure

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

@[vc_gen, simp]
theorem PredTrans.pure_of_post {α} {x : α} : PredTrans.post (· = x) = Pure.pure x := by
  ext p
  exact Iff.intro (fun h => h x (by rfl)) (fun hp y hxy => hxy ▸ hp)

@[vc_gen,simp]
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

@[vc_gen, simp]
theorem PredTrans.pure_post_mono {α} {x : α} {p : α → Prop} : PredTrans.post p ≤ Pure.pure x ↔ ∀ y, p y → y = x := by
  simp only [← pure_of_post, post_mono]

-- for general PredTrans, it seems we cannot prove the equivalence
theorem PredTrans.post_elim {w : PredTrans α} : w ≤ PredTrans.post p → w.val p :=
  fun h => h p (le_refl p)

@[vc_gen, simp]
theorem PredTrans.le_pure_post {α} {x : α} {p : α → Prop} : Pure.pure x ≤ PredTrans.post p ↔ p x := by
  simp only [← PredTrans.pure_of_post, post_mono, forall_eq]

-- Just for future reference
example : PredTrans.post p ≤ Pure.pure x → p ≤ (· = x) := by
  simp[←PredTrans.pure_of_post]
  intros h
  intro y
  exact h y

@[vc_gen]
theorem PredTrans.post_bind_pure {f : α → β} : (do let a ← PredTrans.post p; Pure.pure (f a)) = PredTrans.post (fun b => ∃ a, f a = b ∧ p a) := by
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

section Subst
/-- Backward predicate transformer derived from a substitution property of monads.
A generic effect observation that can be used to observe all monads.
It is oblivious to any computations that happened before it, so `Subst.bind` loses information
for non-pure monads.
It is a suitable choice for the base layer of a specification monad stack if
the observation does the right thing for your use case; see the equivalence lemmas such as
`Obs_Id_eq`.
More sophisticated observations can be built on top of `Subst` by wrapping suitable monad transformers such
as `StateT` or `ExceptT`.
-/
def Subst {m : Type u → Type v} {α} [Monad m] (x : m α) : PredTrans α :=
  ⟨fun p => ∀ {β} {f g : α → m β}, (∀ a, p a → f a = g a) → x >>= f = x >>= g, sorry⟩

notation "Subst⟦" x "⟧" => Subtype.val (Subst x)

theorem Subst.pure [Monad m] [LawfulMonad m]
    (h : p a) : Subst⟦pure (f:=m) a⟧ p := by
  simp_all only [Subst, pure_bind, implies_true]

--set_option pp.all true in
--theorem repro {m : Type u → Type v} {p : α × σ → Prop} [Monad m] [LawfulMonad m] (hp : p (a, s)) :
--  (do Subst (m := StateT σ m) (set s); Subst (m := StateT σ m) (Pure.pure (a, s))) p
--  = Subst (m := StateT σ m) (set s) (fun _ => True)
--  := by
--    replace hp : Subst (m := StateT σ m) (Pure.pure (a, s)) p := (Subst.pure hp)
--    set_option trace.Tactic.rewrites true in
--    conv => lhs; arg 1; intro; rw [eq_true @hp]

theorem Subst.bind [Monad m] [LawfulMonad m] {f : α → m β}
    (hx : Subst⟦x⟧ (fun a => Subst⟦f a⟧ q)) :
    Subst⟦x >>= f⟧ q := by
  intros γ f g hfg
  simp only [bind_assoc]
  exact hx fun a hq => hq hfg

theorem Subst.subst [Monad m] [LawfulMonad m] {x : m α}
  (hp : Subst⟦x⟧ p) (hf : ∀ a, p a → f a = g a) : x >>= f = x >>= g := hp hf

theorem Subst.subst_pre [Monad m] [LawfulMonad m] {x : m α} (hp : Subst⟦x⟧ (fun r => f r = g r)) :
  x >>= f = x >>= g := by apply hp; simp

theorem Subst.conj [Monad m] [LawfulMonad m] {x : m α}
    (hp : Subst⟦x⟧ p) (hq : Subst⟦x⟧ q) : Subst⟦x⟧ (fun r => p r ∧ q r) := by
  intros β f g hfg
  open Classical in
  calc x >>= f
    _ = x >>= (fun r => if p r ∧ q r then f r else f r) := by simp
    _ = x >>= (fun r => if p r ∧ q r then g r else f r) := by simp +contextual [hfg]
    _ = x >>= (fun r => if q r then g r else f r) := hp (by simp +contextual)
    _ = x >>= g := hq (by simp +contextual)

#check Classical.forall_or_exists_not
theorem Subst.inf_conj [Monad m] [LawfulMonad m] {x : m α} {ps : Set (α → Prop)}
    (hp : ∀ p ∈ ps, Subst⟦x⟧ p) : Subst⟦x⟧ (fun r => ∀p ∈ ps, p r) := by
  intros β f g hfg
  replace hp : sInf { Subst⟦x⟧ p | p ∈ ps } := by simp_all only [eq_iff_iff, sInf_Prop_eq,
    Set.mem_setOf_eq, forall_exists_index, and_imp, true_iff, implies_true]
  #check sInf_eq_of_forall_ge_of_forall_gt_exists_lt
  open Classical in
      calc x >>= f
    _ = x >>= (fun r => if ∀ p ∈ ps, p r then f r else f r) := by simp
    _ = x >>= (fun r => if ∀ p ∈ ps, p r then g r else f r) := by simp +contextual [hfg]
--    _ = x >>= (fun r => if ∀ p ∈ ps, p r then g r else g r) := hp _ _ (by simp +contextual [hfg])
  conv => lhs; arg 2; ext r; tactic =>
    match Classical.forall_or_exists_not (fun p => p ∈ ps → p r) with
    | .inl h => simp[hfg r h]; sorry
    | .inr ⟨p, hps⟩ =>
      have : p ∈ ps ∧ ¬ (p r) := Classical.not_imp.mp hps
      exact hp p this.1 (by simp +contextual)
      sorry

theorem Subst.split_unit {m : Type u → Type v} [Monad m] {x : m PUnit} (hp : p) :
  Subst⟦x⟧ (fun _ => p) := fun hfg =>
    funext (fun u => hfg u hp) ▸ rfl

def KimsSubst {m : Type u → Type v} {α} [Functor m] (p : α → Prop) (x : m α) : Prop :=
  (fun r => (r, p r)) <$> x = (fun r => (r, True)) <$> x

def KimsObs_of_Subst {m : Type u → Type v} {α} [Monad m] [LawfulMonad m] (p : α → Prop) (x : m α)
  (h : Subst⟦x⟧ p) : KimsSubst p x := by
  unfold KimsSubst
  simp [← LawfulMonad.bind_pure_comp]
  apply h
  intros
  simp [*]

@[simp]
theorem Obs_Id_eq : Subst⟦x⟧ P ↔ P (Id.run x) := by
  constructor
  case mp =>
    intro h
    replace h := KimsObs_of_Subst P x h
    simp [KimsSubst] at h
    injection h
    simp[*, Id.run]
  case mpr =>
    intro h; apply Subst.pure; exact h

theorem Subst.imp [Monad m] [LawfulMonad m] {p : Prop} {f : α → m β} :
    Subst⟦f a⟧ (fun r => p → q r) ↔ (p → Subst⟦f a⟧ q) := by
  if hp : p
  then simp_all
  else simp_all; intro _ _ _ h; simp[funext (fun a => h a ⟨⟩)]

theorem Subst.mono [Monad m] [LawfulMonad m] {x : m a}
    (h : Subst⟦x⟧ p) (H : ∀ {a}, p a → q a) : Subst⟦x⟧ q := by
    intro _ _ _ hfg
    apply h
    simp_all only [implies_true]

theorem Subst.split_step [Monad m] [LawfulMonad m] {x : m (ForInStep β)}
    {done : β → Prop} {yield : β → Prop}
    (hyield : Subst⟦x⟧ (∀ b', · = .yield b' → yield b'))
    (hdone :  Subst⟦x⟧ (∀ b', · = .done b'  → done b')) :
    Subst⟦x⟧ (fun | .yield b' => yield b' | .done b' => done b') := by
  apply Subst.mono (Subst.conj hyield hdone)
  rintro a ⟨hyield, hdone⟩
  split <;> solve_by_elim

theorem Subst.forIn_list
  [Monad m] [LawfulMonad m]
  {xs : List α} {init : β} {f : α → β → m (ForInStep β)}
  (inv : List α → β → Prop)                     -- user-supplied loop invariant
  (hpre : inv xs init)                          -- pre⟦for {inv} xs init f⟧(p)
  (hweaken : ∀ b, inv [] b → p b)               -- vc₁: weaken invariant to postcondition after loop exit
  (hdone : ∀ {hd tl b}, inv (hd::tl) b →        -- vc₂: weaken invariant to precondition of loop body upon loop entry, done case
          Subst⟦f hd b⟧ (∀ b', · = .done b'  → inv [] b'))
  (hyield : ∀ {hd tl b}, inv (hd::tl) b →       -- vc₃: weaken invariant to precondition of loop body upon loop entry, yield case
          Subst⟦f hd b⟧ (∀ b', · = .yield b' → inv tl b')) :
  Subst⟦forIn xs init f⟧ p := by
    induction xs generalizing init
    case nil => simp only [List.forIn_nil]; apply Subst.pure; apply hweaken; exact hpre
    case cons hd tl h =>
      simp only [List.forIn_cons]
      apply Subst.bind
      have : Subst⟦f hd init⟧ (fun | .yield b' => inv tl b' | .done b' => inv [] b') :=
        Subst.split_step (hyield hpre) (hdone hpre)
      apply Subst.mono this
      intro r hres
      match r with
      | .done b => apply Subst.pure; apply hweaken; assumption
      | .yield b => simp; simp at hres; exact @h b hres

theorem Subst.forIn_range
  [Monad m] [LawfulMonad m]
  {xs : Std.Range} {init : β} {f : Nat → β → m (ForInStep β)}
  (inv : List Nat → β → Prop := fun _ => p)     -- user-supplied loop invariant
  (hpre : inv (List.range' xs.start xs.size xs.step) init)                          -- pre⟦for {inv} xs init f⟧(p)
  (hweaken : ∀ b, inv [] b → p b)               -- vc1: weaken invariant to postcondition after loop exit
  (hdone : ∀ {hd tl b}, inv (hd::tl) b →        -- vc₂: weaken invariant to precondition of loop body upon loop entry, done case
          Subst⟦f hd b⟧ (∀ b', · = .done b'  → inv [] b'))
  (hyield : ∀ {hd tl b}, inv (hd::tl) b →       -- vc₃: weaken invariant to precondition of loop body upon loop entry, yield case
          Subst⟦f hd b⟧ (∀ b', · = .yield b' → inv tl b')) :
  Subst⟦forIn xs init f⟧ p := by
    rw [Std.Range.forIn_eq_forIn_range']
    exact Subst.forIn_list inv hpre hweaken hdone hyield

theorem Subst.forIn_loop
  [Monad m] [LawfulMonad m]
  {xs : Loop} {init : β} {f : Unit → β → m (ForInStep β)}
  (inv : Bool → β → Prop := fun _ => p)     -- user-supplied loop invariant
  (hpre : inv true init)                          -- pre⟦for {inv} xs init f⟧(p)
  (hweaken : ∀ b, inv false b → p b)               -- vc1: weaken invariant to postcondition after loop exit
  (hdone : ∀ {b}, inv true b →        -- vc₂: weaken invariant to precondition of loop body upon loop entry, done case
          Subst⟦f () b⟧ (∀ b', · = .done b'  → inv false b'))
  (hyield : ∀ {b}, inv true b →       -- vc₃: weaken invariant to precondition of loop body upon loop entry, yield case
          Subst⟦f () b⟧ (∀ b', · = .yield b' → inv true b')) :
  Subst⟦forIn Loop.mk init f⟧ p := sorry

end Subst

section MonadOrdered

class MonadOrdered (w : Type u → Type v) [∀{α},Preorder (w α)] extends Monad w, LawfulMonad w where
  -- the following theorem combines
  -- * substitutivity (x ≤ y → x >>= f ≤ y >>= f)
  -- * congruence (f ≤ g → x >>= f ≤ x >>= g)
  bind_mono : ∀{α β} {x y : w α} {f g : α → w β}, x ≤ y → f ≤ g → x >>= f ≤ y >>= g

attribute [simp] MonadOrdered.bind_mono

@[simp]
theorem MonadOrdered.map_mono {α β} [∀{α},Preorder (w α)] [MonadOrdered w] (f : α → β) (x y : w α) (h : x ≤ y) : f <$> x ≤ f <$> y := by
  simp only [←bind_pure_comp]
  exact bind_mono h (by rfl)

theorem MonadOrdered.bind_mono_sup {w : Type u → Type v} {x y : w α} {f : α → w β} [∀{α}, SemilatticeSup (w α)] [MonadOrdered w] :
  (x >>= f) ⊔ (y >>= f) ≤ x ⊔ y >>= f:= by
  have hx : x >>= f ≤ x ⊔ y >>= f := MonadOrdered.bind_mono le_sup_left (le_refl f)
  have hy : y >>= f ≤ x ⊔ y >>= f := MonadOrdered.bind_mono le_sup_right (le_refl f)
  exact sup_le hx hy

instance PredTrans.instMonadOrdered : MonadOrdered PredTrans where
  bind_mono := by
    intros _ _ x y f g hxy hfg --p hxf fixup fallout from Subtype. Want `ext p`; doesn't work
    simp[Bind.bind,PredTrans.bind] at *
--    apply hxy
--    exact x.property (fun a => (f a).val p) _ (fun a => hfg a p) hxf

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
attribute [vc_gen] Observation.pure_pure Observation.bind_bind
attribute [simp] Observation.pure_pure Observation.bind_bind

/-- An expression's spec is a predicate transformer that is an upper bound on the observation of a program -/
abbrev Observation.Spec [Monad m] [∀{α}, Preorder (w α)] [Observation m w] (x : m α) :=
  { wp : w α // Observation.observe x ≤ wp }

class ObservationState (σ : Type u) (m : Type u → Type v) (w : Type u → Type x) [∀{α}, LE (w α)] [Monad m] [MonadStateOf σ m] extends MonadStateOf σ w, Observation m w where
  get_get : observe MonadState.get = MonadState.get
  set_set : observe (MonadStateOf.set s) = MonadStateOf.set (σ := σ) s
attribute [vc_gen] ObservationState.get_get ObservationState.set_set

instance Id.instObservation : Observation Id PredTrans where
  observe := pure
  pure_pure := by simp
  bind_bind := by simp
--instance Subst.instObservation [Monad m] [LawfulMonad m] : Observation m PredTrans where
--  observe := Subst
--  pure_pure := by
--    intros _ a
--    ext p
--    constructor
--    case mpr => simp[Pure.pure, PredTrans.pure]; exact Subst.pure
--    case mp => sorry -- not sure if possible!
--  bind_bind := by
--    intros _ _ x f
--    ext p
--    simp
--    constructor
--    case mpr => sorry
--    case mp => sorry
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

def someProgram : StateT Nat Id Nat := do
  let x ← get
  set (x * 2)
  return x

theorem someProgram_spec : ((StateT.instObservationState.observe someProgram).run s : PredTrans (Nat × Nat)) = pure (s, s*2) := by
  unfold someProgram
  vc_gen

def ExceptT.observe [Monad m] [Monad w] [base : Observation m w] (x : ExceptT ε m α) : ExceptT ε w α :=
  ExceptT.mk (base.observe (ExceptT.run x))
instance ExceptT.instObservation [Monad m] [Monad w] [base : Observation m w] : Observation (ExceptT ε m) (ExceptT ε w) where
  observe := ExceptT.observe
  pure_pure := base.pure_pure
  bind_bind := by
    intros _ _ x f
    have h : ExceptT.bindCont (ExceptT.observe ∘ f) = base.observe ∘ (ExceptT.bindCont f) := by
      ext x
      simp[ExceptT.bindCont,ExceptT.observe]
      split
      · rfl
      · simp only [base.pure_pure]
    simp[ExceptT.run,Bind.bind,ExceptT.bind,ExceptT.bindCont]
    simp[h,ExceptT.observe,base.bind_bind]
    rfl

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
@[vc_gen]
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

-- @[vc_gen 99999999999999]
theorem Observation.Id_pure_eq : Observation.observe (e : Id α) = pure e := Observation.pure_pure

end Observation

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

gen_injective_theorems% ForInStep

-- the following two lemmas are actually a bit ineffective because post_bind_pure
-- wins when a and b are representable by post. Also, often it's not a plain map
-- but rather `fun a => .yield (a + hd)`, and then we would need to exploit general
-- injectivity.
@[simp,vc_gen]
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

@[simp,vc_gen]
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

-- ineffective; just uses if / cases
--@[vc_gen]
--theorem PredTrans.if_then_else {x y : m α} {b : Bool} [Monad m] [∀{α}, LE (w α)] [Observation m w] :
--  Observation.observe (if b then x else y) = if b then Observation.observe x else Observation.observe y := by
--    cases b <;> simp

theorem use_spec {w : Type u → Type x} {f : α → w β} {x y : w α} {goal : w β} [∀ {α}, Preorder (w α)] [MonadOrdered w]
  (hrw : x ≤ y) (hgoal : y >>= f ≤ goal) : x >>= f ≤ goal :=
  le_trans (MonadOrdered.bind_mono hrw (by rfl)) hgoal

theorem test_3 : Observation.observe (do let mut x := 0; for i in [1:5] do { x := x + i }; pure (f := Idd) (); return x) ≤ PredTrans.post (· < 30) := by
  vc_gen
  apply le_trans (Observation.forIn_range ?inv ?hpre ?hstep) ?hgoal
  case inv => exact fun xs => PredTrans.post fun r => (∀ x, x ∈ xs → x ≤ 5) ∧ r + xs.length * 5 ≤ 25
  case hpre => simp_arith
  case hstep => simp_arith; vc_gen; intro hd tl; left; simp_arith; intro r x h h1 h2; subst h; simp_all; omega
  case hgoal => simp_arith

theorem test_3_2 : Observation.observe (do let mut x := 0; for i in [1:5] do { x := x + i }; pure (f := Idd) (); return x) ≤ pure 10 := by
  vc_gen
  apply le_trans (Observation.forIn_range ?inv ?hpre ?hstep) ?hgoal
  case inv => exact fun xs => PredTrans.post fun r => r + xs.sum = 10
  case hpre => simp_arith
  -- sigh. the following could be much better! TODO
  case hstep => simp_arith; vc_gen; intro hd tl; left; simp_arith; intro r x h h1; subst h; simp_all
  case hgoal => simp

-- TBD: Figure out while loops
theorem test_4 : Observation.observe (do let mut x := 0; let mut i := 0; while i < 4 do { x := x + i; i := i + 1 }; pure (f := Idd) (); return x) ≤ pure 6 := by
  vc_gen
  apply use_spec (Observation.forIn_loop ?term ?inv ?hpre ?hstep) ?hgoal
  case term => sorry
  case inv => exact PredTrans.post fun | ⟨i, x⟩ => x + (List.range' i (4-i) 1).sum = 6
  case hpre => simp_arith
  case hstep => sorry
  case hgoal => vc_gen; sorry -- later: conv => lhs; arg 1; intro x; tactic =>

theorem test_1 : Observation.observe (do let mut id := 5; id := 3; pure (f := Id) id) ≤ pure 3 := by
  vc_gen

theorem test_2 : Observation.observe (do let mut x := 5; if x > 1 then { x := 1 } else { x := x }; pure (f:=Id) x) ≤ pure 1 := by
  vc_gen

theorem test_2_2 : Observation.observe (do let mut id := 5; id := 3; pure (f := Id) id) ≤ PredTrans.post (· < 20) := by
  vc_gen

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
      vc_gen
      apply use_spec (Observation.forIn_list ?inv ?hpre ?hstep) ?hgoal
      case inv => exact fun xs => PredTrans.post fun f_H => ∀ i j, f_H i j → 2*t-1 < dist f_H s(i,j)
      case hpre => simp
      case hstep => vc_gen; intro e es; left; sorry
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

macro (name := vc_spec_Idd) "vc_spec_Idd " n:ident post:term : tactic =>
  `(tactic|(unfold $n; apply (Idd.observe_post (p := $post)).mp; vc_gen))

theorem fib_correct {n} : fib_impl n = fib_spec n := by
  -- unfold fib_impl; apply (Idd.observe_post (p := (· = fib_spec n))).mp; vc_gen
  vc_spec_Idd fib_impl (· = fib_spec n)
  if h : n = 0 then vc_gen[h,fib_spec] else ?_
  vc_gen [h,fib_spec]
  apply use_spec (Observation.forIn_range ?inv ?hpre ?hstep)
  case inv => exact fun xs => PredTrans.post fun
    | ⟨a, b⟩ => let i := n - xs.length; xs.length < n ∧ a = fib_spec (i-1) ∧ b = fib_spec i
  case hpre => simp_arith [Nat.succ_le_of_lt, Nat.zero_lt_of_ne_zero h, Nat.sub_sub_eq_min]
  case hstep =>
    simp_arith
    intro tl
    left
    vc_gen
    simp_arith
    intro r ⟨a, b⟩ hr h1 h2 h3
    subst hr
    replace h1 : tl.length + 1 < n := Nat.add_one_le_iff.mpr h1
    simp_arith[Nat.succ_le_of_lt, Nat.zero_lt_of_ne_zero h, Nat.sub_sub_eq_min, Nat.sub_sub, Nat.lt_of_succ_lt] at *
    simp[Nat.lt_of_succ_lt h1,h2,h3]
    refine (fib_spec_rec ?_).symm
    simp_arith[Nat.le_sub_of_add_le' h1]
  vc_gen
  simp_arith
  intro y ⟨a, b⟩ h
  subst h
  simp

end fib
/-
https://lean-fro.zulipchat.com/#narrow/channel/398861-general/topic/baby.20steps.20towards.20monadic.20verification

-/


theorem Tmp.get {m : Type u → Type v} {w : Type u → Type x}
    [Monad m] [Monad w] [LawfulMonad w] [∀{α}, Lattice (w α)] [MonadOrdered w] [obs : Observation m w] :
    Observation.observe get ≤ pure s := sorry

theorem bleh {a : α} {s : σ} : (fun p => p (a, s)) → (do s ← Subst get; Subst (Pure.pure (a, s))) := by
  intro h
  simp only [observe]
  vc_gen
  assumption

theorem StateT.observe.pure {m : Type u → Type v} {p : α × σ → Prop} [Monad m] [LawfulMonad m]
  (hp : p (a, s)) : StateT.observe (m:=m) (pure a) s p := by
  simp only [observe, pure_bind, LawfulMonadState.set_get]
  vc_gen
  assumption

theorem StateT.observe.get_pre {m : Type u → Type v} [Monad m] [LawfulMonad m] {p : σ × σ → Prop} (hp : p ⟨s, s⟩) :
  StateT.observe (m:=m) get s p := by
  simp only [observe, pure_bind, LawfulMonadState.set_get]
  vc_gen
  assumption

theorem StateT.observe.get {m : Type u → Type v} [Monad m] [LawfulMonad m] :
  StateT.observe (m:=m) get s (· = ⟨s, s⟩) := StateT.observe.get_pre (by rfl)

theorem StateT.observe.set_pre {m : Type u → Type v} [Monad m] [LawfulMonad m] {p : PUnit × σ → Prop} (hp : p ⟨⟨⟩, s₂⟩) :
  StateT.observe (m:=m) (set s₂) s₁ p := by
  simp only [observe, pure_bind, Monad.bind_unit]
  simp only [← LawfulMonad.bind_assoc, LawfulMonadState.set_set]
  simp only [LawfulMonadState.set_get_pure]
  simp [-LawfulMonad.bind_pure_comp]
  vc_gen
  assumption

theorem StateT.observe.set {m : Type u → Type v} [Monad m] [LawfulMonad m] {s₂ : σ} :
  StateT.observe (m:=m) (set s₂) s₁ (· = ⟨⟨⟩, s₂⟩) := StateT.observe.set_pre (by rfl)


/-
def fib_spec : Nat → Nat
| 0 => 0
| 1 => 1
| n+2 => fib_spec n + fib_spec (n+1)

theorem fib_spec_rec (h : n > 1) : fib_spec n = fib_spec (n-2) + fib_spec (n-1) := by
  rw (occs := .pos [1]) [fib_spec.eq_def]
  split
  repeat omega
  --omega
  simp

def fib_impl (n : Nat) := Id.run do
  if n = 0 then return 0
  let mut i := 1
  let mut a := 0
  let mut b := 0
  b := b + 1
  while@first_loop i < n do
    let a' := a
    a := b
    b := a' + b
    i := i + 1
    if n > 15 then return 42
  return b

theorem blah : let i := 1; ¬(n = 0) → i ≤ n := by intro _ h; have : _ := Nat.succ_le_of_lt (Nat.zero_lt_of_ne_zero h); assumption

theorem fib_correct : fib_impl n = fib_spec n := by
  unfold fib_impl
  split -- if_split n = 0
  case isTrue  h => simp[h, fib_spec]; exact (Id.pure_eq 0)
  case isFalse h =>
  let_mut_intro i a b' -- i = 1, a = 0, b' = 0.
  let_mut_upd b        -- b = b' + 1
  while_inv (1 ≤ i ∧ i ≤ n ∧ a = fib_spec (i-1) ∧ b = fib_spec i)
  case base => by
    -- goal: show invariant
    -- (weirdness: hcond and hind are not in scope here!
    rw[Nat.sub_self, fib_spec, fib_spec]; sorry
  case induct hcond hinv => by
    -- hcond : i < n
    -- hinv : ...
    -- goal: new(hinv). Q: How do we display this in the goal view?
    let_intro a' ha'  -- ha' : a' = a.     Very similar to intro?
    let_mut_upd a ha  -- ha : a = b         (a' = a†, hcond = ..., hinv = ...)
    let_mut_upd b hb  -- hb : b = a' + b†   (a = b†, ...)
    let_mut_upd i hi  -- hi : i = i† + 1
    -- Now:
    -- hcond : i† < n
    -- hinv : 1 ≤ i† ∧ i ≤ n ∧ a† = fib_spec (i†-1) ∧ b† = fib_spec i†
    have hi1 : i > 1              := by ... hi ... hinv ...
    have     : i ≤ n              := by ... hi ... hinv ...
    have     : a = fib_spec (i-1) := by rw[ha, hinv, hi]
    have     : b = fib_spec i     := by rw[hb, ha', hinv, hinv, (fib_spec_rec hi1).symm]
    show 1 ≤ i ∧ i ≤ n ∧ a = fib_spec (i-1) ∧ b = fib_spec i
    by ⟨by simp_arith[hi1], by assumption, by assumption, by assumption⟩
  intro (hafter : ¬(i < n))
  intro (hinv : ...)
  have i = n          := by simp[hinv, hafter]
  have b = fib_spec n := by simp[this, hinv]
  return_post this

theorem fib_correct_david : fib_impl n = fib_spec n := by
  unfold fib_impl
  do =>
    if n = 0 then by simp[h, fib_spec]
    let mut i a b'
    b := _
    while hcond -- : i < n
          (n - i)
          (hinv : 1 ≤ i ∧ i ≤ n ∧ a = fib_spec (i-1) ∧ b = fib_spec i)
          (by grind ... /- show inv in base case; hinv not in scope here... -/) do
      let a'
      assume a = b;
      a := _
      ----

      ---
      b := _
      i := _
      continue (by ... : 1 ≤ i ∧ i ≤ n ∧ a = fib_spec (i-1) ∧ b = fib_spec i)  /- show inv in inductive case, using old(hinv) and hcond -/)
    return (by ... : b = fib_spec n)

def fib_correct_wlp  : fib_impl n = fib_spec n := Id.run_satisfies2 by
  wlp
    termination first_loop: ...
    invariant   first_loop: 1 ≤ i ∧ i ≤ n ∧ a = fib_spec (i-1) ∧ b = fib_spec i
    by
      /- X goals -/
      grind

def fib_impl_intrinsic (n : Nat) := Id.run do
  if n = 0 then return 0
  let mut i := 1
  let mut a := 0
  let mut b := 0
  b := b + 1
  while i < n
    invariant 1 ≤ i
    invariant i ≤ n
    invariant a = fib_spec (i-1)
    invariant b = fib_spec i
    do
    let a' := a
    a := b
    b := a' + b
    i := i + 1
  return b
-/

def ex (e₁ e₂ : Id Nat) := Id.run do
  let x ← e₁
  let y ← e₂
  pure (x + y)


/--
## Semi-automated verification of monadic programs

Program verification is about

1. Formulating a correctness specification `P` for a program `c`
2. Verifying that `c` satisfies `P`

In Lean, the programs of interest are written using `do`-notation, desugaring to monadic `pure` and `bind` operators of some user-specified monad `M`.

It is tedious to reason about large `do` blocks, because the specification `P` is a postcondition of the program (e.g., for `c = fib_imp 3, P r := r = 8` TODO work out example), while `do`-blocks are fundamentally associated “to-the-right” (forwardly). Furthermore, backward proofs aren’t easily possible because `bind` introduces new binders that are hard to get a handle on without specialised lemmas.

Backward predicate transformer semantics are the standard answer to solving this problem.

### Predicate transformer semantics

Given a postcondition `P : α → Prop` on the result of a program `c : M α`, a *predicate transformer* for `c` is a function `w : (α → Prop) → Prop` such that `w(P)` is a precondition for `c` that ensures `P` "holds on the result of `c`".
(It is an open question whether there is a way to precisely express this property independently of `M`).
For every program, there exists a *weakest* precondition transformer `W` such that every other precondition transformer `w` satisfies `w(P) → W(P)`.
While computing weakest preconditions is impossible for programs involving loops, it is quite mechanical for other every other feature of `do`-blocks, and this is what we propose to automate.

---

Let us write `⟦c⟧(P) : Prop` to say “`c : M α` satisfies postcondition `P : α → Prop`", and let there exist a way to prove `P(c)` from `⟦c⟧(P)`. Then:

- `⟦pure e⟧(P)` iff `P e`
- `⟦bind x f⟧(P)`  iff `⟦x⟧(fun a => ⟦f a⟧(P))`

Applying the valuation `⟦·⟧` manually over the whole `do` block results in a deep nest of proof obligations that is again difficult to visualise and to reason about.
Fortunately, the predicate transformers in the range of the valuation again form a monad, namely the continuation monad `Cont Prop`!
We call `Cont Prop` the *specification monad*, and `M` the *computation monad*.
We may now write
- `⟦pure e⟧(P)` as `(pure e)(P)` (NB: the latter is in `Cont Prop`)
- `⟦bind x f⟧(P)` as `bind ⟦x⟧ ⟦f⟧(P)`
Thus, `⟦·⟧ : ∀{α}, M α → Cont Prop` is a monad morphism, since it maps `pure` to `pure` and `bind` to `bind`, pushing the valuation ever inward.
On a longer `do` block, we get
```
  ⟦do let x ← e₁; let y ← e₂; pure (x + y)⟧(P)
= (do x ← ⟦e₁⟧; y ← ⟦e₂⟧; pure (x + y))(P)
= (do x ← ⟦e₁⟧; y ← ⟦e₂⟧; pure (x + y)(P))
= (do x ← ⟦e₁⟧; y ← ⟦e₂⟧; P (x + y))
```
Which by itself has not achieved *much*, because we are lacking valid predicate transformers for `e₁` and `e₂` to make the binds compute.
This poses a couple of challenges:

- **Challenge 1**: These predicate transformers have to be computed by the user, and we have to provide a way to register them, akin to simp lemmas.
                   Then a simp-like tactic should apply them, generating small verification conditions in turn.
- **Challenge 2**: Can some of these specs be reused, so that the user doesn't to prove them for, e.g., `get` and `set`?
                   Similarly for `foldlM` and `forIn`. This will require a type class algebra in which we can express pre and postconditions.
- **Challenge 3**: We need to be able to add assertions (to aid `grind`) and invariants (for `forIn`) to this setup, with good syntax.
                   This will likely require a way to "navigate" the control flow graph/basic blocks.
                   Alternatively, require that these assertions are provided inline.

An independent set of challenges arises because there is not a single `⟦·⟧` that serves all use cases.
It may be necessary to generalize the entire framework over the choice over the observation `⟦·⟧`, giving rise to "monadic program logic".

### Monadic program logic

There is no single viable implementation of `⟦·⟧`.
To see that, consider first that `Cont Prop` is not the only viable specification monad.
For example,
- When the computation monad is a state monad, the specification monad should have access to the state as well.
- When the computation monad is an exception monad, the specification monad should have access to the exception as well.

Neither is there just a single viable implementation of `⟦·⟧`.
- When the computation monad is non-deterministic, `⟦·⟧` can be chosen to have an angelic (∃ x, P x) or demonic (∀ x, P x) interpretation of the postcondition.
- When the computation monad is `IO`, it is unclear what is the best implementation. Do we only care about input/output, or do we want a separation logic for reasoning about ref cells?

Given that each application comes with its own monad stack, it is hard to anticipate every possible observation.
Therefore we should make it as frictionless as possible for users to plug together their own bespoke observations from a toolbox of building blocks.
This calls for a type class-based approach. Let's call this type class `Observation`.

**Challenge 4**: Which operations should be part of this type class?

This is quite tricky to get right. The type class algebra must be expressive enough to prove monad-polymorphic lemmas.

Here is an example about `forIn`.
I managed to prove the following lemma about `forIn` for a specific specification monad `Subst`:
```
theorem Subst.forIn_list
  [Monad m] [LawfulMonad m]
  {xs : List α} {init : β} {f : α → β → m (ForInStep β)}
  (inv : List α → β → Prop)                     -- user-supplied loop invariant
  (hpre : inv xs init)                          -- pre⟦for {inv} xs init f⟧(p)
  (hweaken : ∀ b, inv [] b → p b)               -- vc₁: weaken invariant to postcondition after loop exit
  (hdone : ∀ {hd tl b}, inv (hd::tl) b →        -- vc₂: weaken invariant to precondition of loop body upon loop entry, done case
          Subst⟦f hd b⟧ (∀ b', · = .done b'  → inv [] b'))
  (hyield : ∀ {hd tl b}, inv (hd::tl) b →       -- vc₃: weaken invariant to precondition of loop body upon loop entry, yield case
          Subst⟦f hd b⟧ (∀ b', · = .yield b' → inv tl b')) :
  Subst⟦forIn xs init f⟧ p := ...
```
This is a nice lemma because it corresponds to the classic precondition transformer for while loops.

**Challenge 4.1**: How would we generalize this lemma beyond `Subst : Cont Prop`? This will influence the type class algebra.

I think we will need a notion of `∀` (infinite conjunction) in addition to implication (modelled by `≤`).
We could then register the `Observation`-generalized version of `Subst.forIn_list` above as the specification of `forIn`.
Other monad-polymorphic functions should get similar treatment, and similarly lead to requirements on the design of `Observation`.

Once the design is final, all that remains is to tweak the simp-like tactic; what remains should be pure verification conditions.

### Discharging verification conditions

... should be possible by a simple call to `simp_all` or `grind`.
We should try very hard to make this as convenient and *fast* as possible.
Verus is an excellent example in this regard; they have taken great lengths to generate verification conditions that the SMT solver is fast to discharge.
The user must help the SMT solver by providing assertions with the right trigger expressions for the SMT solver to instantiate formulas.

Furthermore, Verus integrates a couple of even faster and automated verifiers, such as ones based on ERP (effectively propositional logic), non-linear arithmetic solvers, bit blasters, etc.

In addition to that, Verus integrates a nice transition system centric model for verifying concurrent systems based on ghost resources (but without exposing the user to linear logic).
-/
