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

theorem PreCond.imp_pure_extract_l {ps} {P : Prop} {P' : PreCond ps} {Q : PreCond ps}
  (h : P → P' ≤ Q) : PreCond.pure P ⊓ P' ≤ Q := by
  induction ps
  case pure => simp; exact h
  case arg σ s ih => intro s; apply ih (fun hp => h hp s)
  case except ε s ih => simp; apply ih h

theorem PreCond.imp_pure_extract_r {ps} {P : Prop} {P' : PreCond ps} {Q : PreCond ps}
  (h : P → P' ≤ Q) : P' ⊓ PreCond.pure P ≤ Q := by
  induction ps
  case pure => simp; exact (flip h)
  case arg σ s ih => intro s; apply ih (fun hp => h hp s)
  case except ε s ih => simp; apply ih h

theorem PreCond.imp_pure_extract {ps} {P : Prop} {Q : PreCond ps}
  (h : P → PreCond.pure True ≤ Q) : PreCond.pure P ≤ Q := by
  induction ps
  case pure => simp; intro hp; exact (h hp) .intro
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

@[ext]
structure PredTrans (ps : PredShape) (α : Type) : Type where
  apply : PostCond α ps → PreCond ps

def PredTrans.pure {ps : PredShape} {α : Type} (a : α) : PredTrans ps α :=
  { apply := fun Q => Q.1 a }

def PredTrans.bind {ps : PredShape} {α β : Type} (x : PredTrans ps α) (f : α → PredTrans ps β) : PredTrans ps β :=
  { apply := fun Q => x.apply (fun a => (f a).apply Q, Q.2) }

instance : Monad (PredTrans ps) where
  pure := PredTrans.pure
  bind := PredTrans.bind

def PredTrans.le {ps : PredShape} {α : Type} (x y : PredTrans ps α) : Prop :=
  y.apply ≤ x.apply
noncomputable def PredTrans.top {ps : PredShape} {α : Type} : PredTrans ps α :=
  PredTrans.mk ⊥
noncomputable def PredTrans.bot {ps : PredShape} {α : Type} : PredTrans ps α :=
  PredTrans.mk ⊤
noncomputable def PredTrans.sup {ps : PredShape} {α : Type} : PredTrans ps α → PredTrans ps α → PredTrans ps α :=
  fun x y => PredTrans.mk (x.apply ⊔ y.apply)
noncomputable def PredTrans.inf {ps : PredShape} {α : Type} : PredTrans ps α → PredTrans ps α → PredTrans ps α :=
  fun x y => PredTrans.mk (x.apply ⊓ y.apply)
noncomputable def PredTrans.sSup {ps : PredShape} {α : Type} : Set (PredTrans ps α) → PredTrans ps α :=
  fun x => PredTrans.mk (InfSet.sInf { p | .mk p ∈ x })
noncomputable def PredTrans.sInf {ps : PredShape} {α : Type} : Set (PredTrans ps α) → PredTrans ps α :=
  fun x => PredTrans.mk (SupSet.sSup { p | .mk p ∈ x })

noncomputable instance : CompleteLattice (PredTrans ps α) where
  le := PredTrans.le
  le_refl := by simp [PredTrans.le]
  le_trans := sorry
  le_antisymm := sorry
  sup := PredTrans.sup
  le_sup_left := sorry
  le_sup_right := sorry
  sup_le := sorry
  inf := PredTrans.inf
  le_inf := sorry
  inf_le_left := sorry
  inf_le_right := sorry
  sSup := PredTrans.sSup
  le_sSup := sorry
  sSup_le := sorry
  top := PredTrans.top
  bot := PredTrans.bot
  le_top := sorry
  bot_le := sorry
  sInf := PredTrans.sInf
  le_sInf := sorry
  sInf_le := sorry

@[simp]
theorem PredTrans.pure_apply {ps : PredShape} {α : Type} (a : α) (Q : PostCond α ps) :
  (Pure.pure a : PredTrans ps α).apply Q = Q.1 a := by rfl
--
--@[simp]
--theorem PredTrans.pure_apply2 {ps : PredShape} {α : Type} (a : α) (Q : PostCond α ps) :
--  (PredTrans.pure a).apply Q = Q.1 a := by rfl
--
--@[simp]
--theorem PredTrans.bind_apply {ps : PredShape} {α β : Type} (x : PredTrans ps α) (f : α → PredTrans ps β) (Q : PostCond β ps) :
--  (Bind.bind x f).apply Q = x.apply (fun a => (f a).apply Q, Q.2) := by rfl
--
--@[simp]
--theorem PredTrans.bind_apply2 {ps : PredShape} {α β : Type} (x : PredTrans ps α) (f : α → PredTrans ps β) (Q : PostCond β ps) :
--  (PredTrans.bind x f).apply Q = x.apply (fun a => (f a).apply Q, Q.2) := by rfl
--
@[simp]
theorem PredTrans.map_apply {ps : PredShape} {α β : Type} (f : α → β) (x : PredTrans ps α) (Q : PostCond β ps) :
  (f <$> x).apply Q = x.apply (fun a => Q.1 (f a), Q.2) := by rfl

@[simp]
theorem PredTrans.bind_apply {ps : PredShape} {α β : Type} (f : α → PredTrans ps β) (trans : PostCond α ps → PreCond ps) (Q : PostCond β ps) :
  (Bind.bind { apply := trans } f).apply Q = trans (fun a => (f a).apply Q, Q.2) := by rfl
--
--
--@[simp]
--theorem PredTrans.seq_apply {ps : PredShape} {α β : Type} (f : PredTrans ps (α → β)) (x : PredTrans ps α) (Q : PostCond β ps) :
--  (f <*> x).apply Q = f.apply (fun g => x.apply (fun a => Q.1 (g a), Q.2), Q.2) := by rfl

theorem PredTrans.bind_mono {ps : PredShape} {α β : Type} {x y : PredTrans ps α} {f : α → PredTrans ps β}
  (h : x ≤ y) : x >>= f ≤ y >>= f := by intro Q; apply le_trans (h (_, Q.2)) le_rfl

instance : LawfulMonad (PredTrans ps) where
  bind_pure_comp f x := by simp only [bind, pure, Functor.map, Function.comp_def]
  bind_map f x := by simp only [bind, Functor.map, Function.comp_def, Seq.seq]
  pure_bind x f := by simp +unfoldPartialApp only [bind, PredTrans.bind, pure, PredTrans.pure]
  bind_assoc x f g := by simp +unfoldPartialApp only [bind, PredTrans.bind]
  map_const := sorry
  id_map := sorry
  seqLeft_eq := sorry
  seqRight_eq := sorry
  pure_seq := sorry

class WP (m : Type → Type) (ps : outParam PredShape) where
  wp {α} (x : m α) : PredTrans ps α
  wp_mono {α} (x : m α) (Q₁ Q₂ : PostCond α ps) :
    Q₁ ≤ Q₂ → (wp x).apply Q₁ ≤ (wp x).apply Q₂
open WP

instance Idd.instWP : WP Idd .pure where
  wp x := PredTrans.pure x.run
  wp_mono x _ _ h := h.1 x.run

theorem Idd.by_wp {prog : Idd α} (P : α → Prop) :
  (wp prog).apply (PostCond.total P) → P (Idd.run prog) := id

instance StateT.instWP [Monad m] [WP m ps] : WP (StateT σ m) (.arg σ ps) where
  wp x := { apply := fun Q s => (wp (x s)).apply (fun (a, s') => Q.1 a s', Q.2) }
  wp_mono {α} x Q₁ Q₂ h := by
    intro s
    simp only [wp]
    apply wp_mono (x s)
    simp only [Prod.mk_le_mk, h.2, and_true]
    intro x
    apply h.1

instance ReaderT.instWP [Monad m] [WP m ps] : WP (ReaderT ρ m) (.arg ρ ps) where
  wp x := { apply := fun Q r => (wp (x r)).apply (fun a => Q.1 a r, Q.2) }
  wp_mono x Q₁ Q₂ h := by
    intro r
    simp only [wp]
    apply wp_mono (x r)
    simp only [Prod.mk_le_mk, h.2, and_true]
    intro x
    apply h.1

instance ExceptT.instWP [Monad m] [WP m ps] : WP (ExceptT ε m) (.except ε ps) where
  wp x := { apply := fun Q => (wp (x.run)).apply (fun | .ok a => Q.1 a | .error e => Q.2.1 e, Q.2.2) }
  wp_mono x Q₁ Q₂ h := by
    simp [wp, bind, ExceptT.bind]
    apply wp_mono _ _ _ ?_
    simp[h.2.2]
    intro x
    cases x
    case error e => apply h.2.1 e
    case ok a => apply h.1 a

instance EStateM.instWP : WP (EStateM ε σ) (.except ε (.arg σ .pure)) where
  wp x := { apply := fun Q s => match x s with
    | .ok a s' => Q.1 a s'
    | .error e s' => Q.2.1 e s'
  }
  wp_mono x Q₁ Q₂ h := by
    intro s
    simp[wp]
    cases (x s) <;> apply_rules [h.1,h.2.1]

class LawfulWP (m : Type → Type) (ps : outParam PredShape) [Monad m] [WP m ps] where
  wp_pure {α} (a : α) :
    wp (m:=m) (pure a) = pure a
  wp_bind {α β} (x : m α) (f : α → m β) :
    wp (do let a ← x; f a) = do let a ← wp x; wp (f a)

--theorem LawfulWP.wp_pure_conseq {m : Type → Type} [Monad m] [WP m ps] [LawfulWP m ps] {α} {P : PreCond ps} {Q : PostCond α ps} (a : α)
--    (himp : P ≤ Q.1 a) : P ≤ wp (m:=m) (pure a) Q := by rw[wp_pure a]; exact himp

-- theorem LawfulWP.wp_bind_conseq_f {m : Type → Type} [Monad m] [WP m ps] [LawfulWP m ps] {α β} {P : PostCond α ps} {Q : PostCond β ps} (x : m α) (f : α → m β)
--     (hf : ∀a, P.1 a ≤ wp (f a) Q) (herror : P.2 ≤ Q.2) :
--     wp x P ≤ wp (x >>= f) Q := by rw[wp_bind x f]; exact wp_mono x P (fun a => wp (f a) Q, Q.2) ⟨hf, herror⟩

--theorem LawfulWP.wp_mono_2 {m : Type → Type} [Monad m] [WP m ps] [LawfulWP m ps] {α} (x : m α) (Q₁ Q₂ : PostCond α ps)
--    (h1 : Q₁.1 ≤ Q₂.1) (h2 : Q₁.2 ≤ Q₂.2) :
--    wp x Q₁ ≤ wp x Q₂ := wp_mono x _ _ ⟨h1,h2⟩

theorem LawfulWP.wp_map {m : Type → Type} [Monad m] [LawfulMonad m] [WP m ps] [LawfulWP m ps] (f : α → β) (x : m α) :
  wp (f <$> x) = f <$> wp x := by
    simp [← bind_pure_comp, wp_bind, wp_pure]

theorem LawfulWP.wp_seq {m : Type → Type} [Monad m] [LawfulMonad m] [WP m ps] [LawfulWP m ps] (f : m (α → β)) (x : m α) :
  wp (f <*> x) = wp f <*> wp x := by
    simp [← bind_map, wp_bind, wp_map]

-- theorem LawfulWP.wp_seq_f {m : Type → Type} [Monad m] [LawfulMonad m] [WP m ps] [LawfulWP m ps] (f : m (α → β)) (x : m α) {Q : PostCond β ps}
--     (hx : ∀f, P.1 f ≤ wp x (fun a => Q.1 (f a), Q.2)) (herror : P.2 ≤ Q.2) :
--   wp f P ≤ wp (f <*> x) Q := le_trans (wp_mono f P _ ⟨hx, herror⟩) (wp_seq f x)

theorem LawfulWP.wp_dite {c : Prop} [Decidable c] {t : c → m α} {e : ¬c → m α} [WP m ps] :
  wp (dite c t e) = if h : c then wp (t h) else wp (e h) := by
    split <;> simp

theorem LawfulWP.wp_ite {c : Prop} [Decidable c] {t : m α} {e : m α} [WP m ps] :
  wp (ite c t e) = if c then wp t else wp e := by
  split <;> simp

open LawfulWP

attribute [simp] wp_pure wp_bind wp_map wp_seq wp_dite wp_ite

instance Idd.instLawfulWP : LawfulWP Idd .pure where
  wp_pure a := by simp only [wp, PredTrans.pure, Pure.pure, pure]
  wp_bind x f := by simp only [wp, PredTrans.pure, Bind.bind, bind, PredTrans.bind]

instance StateT.instLawfulWP [Monad m] [WP m ps] [LawfulWP m ps] : LawfulWP (StateT σ m) (.arg σ ps) where
  wp_pure a := by simp [wp, PredTrans.pure, pure, StateT.pure, wp_pure]
  wp_bind x f := by simp [wp, PredTrans.pure, Bind.bind, bind, PredTrans.bind, StateT.bind]

instance ReaderT.instLawfulWP [Monad m] [WP m ps] [LawfulWP m ps] : LawfulWP (ReaderT ρ m) (.arg ρ ps) where
  wp_pure a := by simp [wp, PredTrans.pure, pure, ReaderT.pure, wp_pure]
  wp_bind x f := by simp [wp, PredTrans.pure, Bind.bind, bind, PredTrans.bind, ReaderT.bind]

instance ExceptT.instLawfulWP [Monad m] [WP m ps] [LawfulWP m ps] : LawfulWP (ExceptT ε m) (.except ε ps) where
  wp_pure a := by simp [wp, PredTrans.pure, pure, ExceptT.pure, wp_pure]
  wp_bind x f := by
    ext Q
    simp [wp, bind, ExceptT.bind, run_mk, wp_bind, ExceptT.bindCont, PredTrans.bind]
    congr
    ext b
    cases b
    case error a => simp[PredTrans.pure, pure]
    case ok a => congr

instance EStateM.instLawfulWP : LawfulWP (EStateM ε σ) (.except ε (.arg σ .pure)) where
  wp_pure a := by simp [wp, PredTrans.pure, pure, EStateM.pure]
  wp_bind x f := by
    ext Q s
    simp [wp, bind, EStateM.bind, eq_iff_iff, PredTrans.bind]
    cases (x s) <;> simp

def MonadTriple.triple {m : Type → Type} {ps : PredShape} [WP m ps] {α} (x : m α) (P : PreCond ps) (Q : PostCond α ps) : Prop :=
  P ≤ (wp x).apply Q

open MonadTriple (triple)

theorem LawfulMonadTriple.triple_conseq {m : Type → Type} [WP m ps] {α} (x : m α) {P P' : PreCond ps} {Q Q' : PostCond α ps}
  (hp : P ≤ P' := by simp) (hq : Q' ≤ Q := by simp) (h : triple x P' Q') :
  triple x P Q := by
    apply le_trans hp
    apply le_trans h
    apply wp_mono x Q' Q hq

theorem LawfulMonadTriple.triple_extract_persistent {m : Type → Type} [Monad m] [WP m ps] [LawfulWP m ps] {P : Prop} {P' : PreCond ps} {Q : PostCond α ps}
  (x : m α) (h : P → triple x P' Q) :
  triple x (PreCond.pure P ⊓ P') Q := PreCond.imp_pure_extract h

theorem LawfulMonadTriple.triple_pure {m : Type → Type} [Monad m] [WP m ps] [LawfulWP m ps] {α} {Q : PostCond α ps} (a : α) (himp : P ≤ Q.1 a) :
  triple (pure (f:=m) a) P Q := by apply le_trans himp (by simp only [wp_pure, PredTrans.pure_apply, le_refl])

theorem LawfulMonadTriple.triple_bind {m : Type → Type} [Monad m] [WP m ps] [LawfulWP m ps] {α β} {P : PreCond ps} {Q : α → PreCond ps} {R : PostCond β ps} (x : m α) (f : α → m β)
  (hx : triple x P (Q, R.2))
  (hf : ∀ b, triple (f b) (Q b) R) :
  triple (x >>= f) P R := by
    apply le_trans hx
    simp only [wp_bind]
    apply wp_mono x
    simp only [Prod.mk_le_mk, le_refl, and_true]
    exact hf

theorem LawfulMonadTriple.triple_conseq_l {m : Type → Type} [Monad m] [WP m ps] [LawfulWP m ps] {P P' : PreCond ps} {Q : PostCond α ps}
  (x : m α) (hp : P ≤ P') (h : triple x P' Q) :
  triple x P Q := triple_conseq x hp le_rfl h

theorem LawfulMonadTriple.triple_conseq_r {m : Type → Type} [Monad m] [WP m ps] [LawfulWP m ps] {P : PreCond ps} {Q Q' : PostCond α ps}
  (x : m α) (hq : Q ≤ Q') (h : triple x P Q) :
  triple x P Q' := triple_conseq x le_rfl hq h

--theorem LawfulMonadTriple.triple_map {m : Type → Type} [Monad m] [LawfulMonad m] [WP m ps] [LawfulWP m ps] (f : α → β) (x : m α)
--  (h : triple x P (fun a => Q.1 (f a), Q.2)) :
--  triple (f <$> x) P Q := by
--    simp only [← bind_pure_comp]
--    apply triple_bind _ _ h
--    intro b
--    apply triple_pure
--    simp only [le_refl]

--theorem LawfulMonadTriple.triple_seq {m : Type → Type} [Monad m] [LawfulMonad m] [WP m ps] [LawfulWP m ps] (f : m (α → β)) (x : m α) {Q : (α → β) → PreCond ps}
--  (hf : triple f P (Q, R.2))
--  (hx : ∀ f, triple x (Q f) (fun a => R.1 (f a), R.2)) :
--  triple (f <*> x) P R := by
--    simp only [← bind_map]
--    apply triple_bind _ _ hf ?_
--    intro f
--    apply triple_map _ _ (hx f)

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

def PredTrans.frame_arg (p : PredTrans m α) : PredTrans (.arg σ m) α :=
  { apply Q s := p.apply (fun a => Q.1 a s, Q.2) }

instance PredTrans.liftArg : MonadLift (PredTrans m) (PredTrans (.arg σ m)) where
  monadLift := PredTrans.frame_arg

def PredTrans.drop_fail_cond (Q : PostCond α (.except σ m)) : PostCond α m :=
  (Q.1, Q.2.2)

instance PredTrans.instExcept : MonadLift (PredTrans m) (PredTrans (.except σ m)) where
  monadLift p := { apply := p.apply ∘ PredTrans.drop_fail_cond }

class LawfulWPLift (m : semiOutParam (Type → Type)) (n : Type → Type) (psm : outParam PredShape) (psn : outParam PredShape)
  [WP m psm] [WP n psn] [MonadLift m n] [MonadLift (PredTrans psm) (PredTrans psn)] where
  wp_monadLift {x : m α} :
    wp (MonadLift.monadLift x : n α) = MonadLift.monadLift (wp x)

open LawfulWPLift

attribute [simp] LawfulWPLift.wp_monadLift

instance StateT.instLawfulWPLift [Monad m] [WP m psm] [LawfulMonad m] [LawfulWP m psm] : LawfulWPLift m (StateT σ m) psm (.arg σ psm) where
  wp_monadLift := by simp[wp, liftM, MonadLift.monadLift, StateT.lift, PredTrans.frame_arg]

instance ExceptT.instLawfulWPLift [Monad m] [WP m psm] [LawfulMonad m] [LawfulWP m psm] : LawfulWPLift m (ExceptT ε m) psm (.except ε psm) where
  wp_monadLift := by simp[wp, liftM, MonadLift.monadLift, ExceptT.lift, Function.comp_def, PredTrans.drop_fail_cond]

-- @[simp]
theorem StateT.wp_get [WP m sh] [Monad m] [LawfulWP m sh] :
  wp (MonadStateOf.get : StateT σ m σ) = { apply := fun Q s => Q.1 s s } := by
    simp[wp, MonadState.get, getThe, MonadStateOf.get, StateT.get, pure, PredTrans.pure]

-- @[simp]
theorem MonadStateOf.wp_get [WP m msh] [WP n nsh] [MonadLift m n] [MonadLift (PredTrans msh) (PredTrans nsh)] [MonadStateOf σ m] [LawfulWPLift m n msh nsh] :
  wp (MonadStateOf.get : n σ) = MonadLift.monadLift (wp (MonadStateOf.get : m σ)) := by
    simp [MonadStateOf.get, liftM, monadLift]

-- @[simp]
theorem MonadState.wp_get [WP m sh] [MonadStateOf σ m] :
  wp (MonadState.get : m σ) = wp (MonadStateOf.get : m σ) := rfl

--@[simp]
theorem StateT.wp_set [WP m sh] [Monad m] [LawfulWP m sh] (x : σ) :
  wp (set x : StateT σ m PUnit) = { apply := fun Q _ => Q.1 ⟨⟩ x } := by
    simp[wp, MonadState.set, MonadStateOf.set, StateT.set, pure, PredTrans.pure]

--@[simp]
theorem MonadStateOf.wp_set [WP m msh] [WP n nsh] [MonadLift m n] [MonadLift (PredTrans msh) (PredTrans nsh)] [MonadStateOf σ m] [LawfulWPLift m n msh nsh] :
  wp (MonadStateOf.set x : n PUnit) = MonadLift.monadLift (wp (MonadStateOf.set (σ:=σ) x : m PUnit)) := by
    simp [MonadStateOf.set, liftM, monadLift]

-- @[simp]
theorem MonadState.wp_set [WP m sh] [MonadStateOf σ m] :
  wp (MonadState.set x : m PUnit) = wp (MonadStateOf.set x : m PUnit) := rfl

theorem ExceptT.throw_spec [Monad m] [WP m stack] [LawfulWP m stack] :
  wp (throw e : ExceptT ε m σ) = { apply := fun Q => Q.2.1 e } := by
    simp[wp, pure, PredTrans.pure]

--def LawfulMonadLiftTripleT.triple_lift {m n : Type → Type} {psm : PredShape} {psn : PredShape}
--  [MonadLiftT m n] [WP m psm] [WP n psn] [inst : LawfulWPLiftT m n psm psn] {x : m α} {P : PreCond psm} {Q : PostCond α psm}
--  (h : triple x P Q) :
--  triple (m:=n) (liftM x) (inst.lift_pred_impl.lift_pre P) (inst.lift_pred_impl.lift_post Q) :=
--    le_trans (inst.lift_pred_impl.lift_pre_conseq h) inst.wp_lift
--
--def LawfulMonadLiftTripleT.triple_lift_r [Monad n] [MonadLiftT m n] [WP m psm] [WP n psn] [LawfulWP n psn] [inst : LawfulWPLiftT m n psm psn] {x : m α} {P : PreCond psm} {Q : PostCond α psm} {Q' : PostCond α psn}
--  (h : triple x P Q) (h' : inst.lift_pred_impl.lift_post Q ≤ Q') :
--  triple (m:=n) (liftM x) (inst.lift_pred_impl.lift_pre P) Q' := triple_conseq_r _ h' (triple_lift h)
--
--def LawfulMonadLiftTripleT.triple_lift_l [Monad n] [MonadLiftT m n] [WP m psm] [WP n psn] [LawfulWP n psn] [inst : LawfulWPLiftT m n psm psn] {x : m α} {P' : PreCond psn} {P : PreCond psm}
--  (h : triple x P Q) (h' : P' ≤ inst.lift_pred_impl.lift_pre P) :
--  triple (m:=n) (liftM x) P' (inst.lift_pred_impl.lift_post Q) := triple_conseq_l _ h' (triple_lift h)
--
--def LawfulMonadLiftTripleT.triple_lift_conseq [Monad n] [MonadLiftT m n] [WP m psm] [WP n psn] [LawfulWP n psn] [inst : LawfulWPLiftT m n psm psn] {x : m α} {P : PreCond psm} {Q : PostCond α psm} {P' : PreCond psn} {Q' : PostCond α psn}
--  (hp : P' ≤ inst.lift_pred_impl.lift_pre P) (hq : inst.lift_pred_impl.lift_post Q ≤ Q') (h : triple x P Q) :
--  triple (m:=n) (liftM x) P' Q' := triple_conseq _ hp hq (triple_lift h)
--
--open LawfulMonadLiftTripleT (triple_lift triple_lift_r triple_lift_l)

notation:lead "⦃" P "⦄ " x:lead " ⦃" Q "⦄" =>
  MonadTriple.triple x P Q
notation:lead "⦃" P "⦄ " x:lead " ⦃⇓" v " | " Q "⦄" =>
  ⦃P⦄ x ⦃PostCond.total fun v => Q⦄
notation:lead "⟦" e "⟧" =>
  WP.wp e

section CFML

theorem xwp_lemma {m : Type → Type} [WP m ps] {α} {x : m α} {P : PreCond ps} {Q : PostCond α ps} :
  P ≤ (wp x).apply Q → ⦃P⦄ x ⦃Q⦄ := id

theorem triple_to_wp {m : Type → Type} {ps : PredShape} [WP m ps] {α} {x : m α} {P : PreCond ps} {Q : PostCond α ps}
  (h : ⦃P⦄ x ⦃Q⦄) :
  wp x ≤ { apply := fun Q' => P ⊓ PreCond.pure (Q ≤ Q')} := by
  intro Q₂
  simp
  apply PreCond.imp_pure_extract_r
  intro hq
  exact le_trans h (wp_mono x _ _ hq)

theorem rw_wp {m : Type → Type} {ps : PredShape} [WP m ps] {α} {x : m α} {t : PredTrans ps α}
  (h : wp x = t): wp x ≤ t := h ▸ le_rfl

syntax "xwp" notFollowedBy("|") (ppSpace colGt term:max)* : tactic

macro_rules
  | `(tactic| xwp) => `(tactic| (refine xwp_lemma ?_; simp +contextual)) -- contextual needed in test_3 below. TODO: try with grind
  | `(tactic| xwp $x $xs*) => `(tactic| (refine xwp_lemma ?_; simp +contextual; intro $x $xs*))

end CFML

theorem Triple.forIn_list {α β} {m : Type → Type}
  [Monad m] [LawfulMonad m] [WP m ps] [LawfulWP m ps]
  {xs : List α} {init : β} {f : α → β → m (ForInStep β)}
  (inv : PostCond (List α × β) ps)
  (hstep : ∀ hd tl b,
      ⦃inv.1 (hd :: tl, b)⦄
      (f hd b)
      ⦃(fun r => match r with | .yield b' => inv.1 (tl, b') | .done b' => inv.1 ([], b'), inv.2)⦄) :
  ⦃inv.1 (xs, init)⦄ (forIn xs init f) ⦃(fun b' => inv.1 ([], b'), inv.2)⦄ := by
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
  (hstep : ∀ hd tl b,
      ⦃inv.1 (hd :: tl, b)⦄
      (f b hd)
      ⦃(fun b' => inv.1 (tl, b'), inv.2)⦄) :
  ⦃inv.1 (xs, init)⦄ (List.foldlM f init xs) ⦃(fun b' => inv.1 ([], b'), inv.2)⦄ := by
  have : xs.foldlM f init = forIn xs init (fun a b => .yield <$> f b a) := by
    simp only [List.forIn_yield_eq_foldlM, id_map']
  rw[this]
  apply Triple.forIn_list inv
  simp only [triple, wp_map, PredTrans.map_apply]
  exact hstep

end Triple

section IO

axiom IO.wp {α ε} (x : EIO ε α) : PredTrans (.except ε .pure) α
axiom IO.wp_mono {α ε} (x : EIO ε α) (Q Q' : PostCond α (.except ε .pure)) :
  Q ≤ Q' → (IO.wp x).apply Q ≤ (IO.wp x).apply Q'
axiom IO.wp_pure {α ε} (a : α) :
  IO.wp (pure (f := EIO ε) a) = PredTrans.pure a
axiom IO.wp_bind {α β ε} (x : EIO ε α) (f : α → EIO ε β) :
  IO.wp (x >>= f) = IO.wp x >>= fun a => IO.wp (f a)

noncomputable instance IO.instWP : WP (EIO ε) (.except ε .pure) where
  wp := IO.wp
  wp_mono := IO.wp_mono

noncomputable instance IO.instLawfulWP : LawfulWP (EIO ε) (.except ε .pure) where
  wp_pure := IO.wp_pure
  wp_bind := IO.wp_bind

end IO

gen_injective_theorems% ForInStep

syntax "xapp" (ppSpace colGt term:max) : tactic

partial def xapp (target : Expr) (spec : TSyntax `term) : TacticM Unit := withMainContext do
  let rec loop (trans : Expr) (goal : MVarId) : TacticM Unit := do
    match_expr trans with
    | WP.wp m ps instWP α x =>
      let P ← liftMetaM <| mkFreshExprMVar (mkApp (mkConst ``PreCond) ps)
      let Q ← liftMetaM <| mkFreshExprMVar (mkApp2 (mkConst ``PostCond) α ps)
      let triple_ty ← mkAppM ``MonadTriple.triple #[x, P, Q]
      try
        let spec ← elabTerm spec triple_ty
        let triple_to_wp_app ← mkAppM ``triple_to_wp #[spec]
        let gs ← liftMetaM <| goal.apply triple_to_wp_app
        pushGoals gs
      catch _ =>
        return
        -- `spec` might have type `wp x = t`. Try `rw_wp`
  --      let y ← liftMetaM <| mkFreshExprMVar (← inferType x) (userName := `y)
  --      let .forallE _ h_ty _ _ ← inferType (mkApp6 (mkConst ``PredTrans.bind_mono) ps α β x y f) | failure
  --      let_expr LE.le _α _inst a b  := h_ty | throwError "xapp: wrong type {h_ty}"
  --      let eq_ty ← mkAppM ``Eq #[a, b]
  --      let spec ← elabTerm spec eq_ty
  --      let gs ← liftMetaM <| h_mvar.apply (← mkAppM ``rw_wp #[spec])
        -- replaceMainGoal (← liftMetaM <| goal.apply (← mkAppM ``rw_wp #[spec]))
    | Bind.bind m _instBind α β x f =>
      let_expr PredTrans ps := m | throwError "xapp: wrong monad {m}"
      let y ← liftMetaM <| mkFreshExprMVar (← inferType x) (userName := `y)
      let .forallE _ h_ty _ _ ← inferType (mkApp6 (mkConst ``PredTrans.bind_mono) ps α β x y f) | failure
      let h ← liftMetaM <| mkFreshExprMVar h_ty (userName := `h)
      pushGoals (← liftMetaM <| goal.apply (mkApp7 (mkConst ``PredTrans.bind_mono) ps α β x y f h))
      let .mvar h_mvar := h | failure
      -- now solve `h_mvar`
      loop x h_mvar

    | _ => throwError "xapp: unsupported term" -- {tgt.getArg! 2}"
  loop (target.getArg! 2) (← getMainGoal)

elab "xapp" spec:term : tactic => withMainContext do
  let tgt ← getMainTarget
  if not (tgt.isAppOf `PredTrans.apply) then throwError "xapp: unsupported term"
  xapp tgt spec

theorem test_ex :
  ⦃fun s => s = 4⦄
  (do let mut x := 0
      let s ← get
      for i in [1:s] do { x := x + i; if x > 4 then throw 42 }
      (set 1 : ExceptT Nat (StateT Nat Idd) PUnit)
      return x)
  ⦃(fun r s => False,
    fun e s => e = 42 ∧ s = 4,
    ())⦄ := by
  xwp s hs
  conv in (bind (WP.wp _)) =>
    simp only [MonadState.wp_get, MonadStateOf.wp_get, StateT.wp_get, MonadLift.monadLift, Function.comp_def, PredTrans.drop_fail_cond]
  simp only [PredTrans.bind_apply]
  xapp -- this is like the conv in (bind (WP.wp _)) above, but based on monotonicity
    (Triple.forIn_list (fun (xs, r) s => r ≤ 4 ∧ s = 4 ∧ r + xs.sum > 4, fun e s => e = 42 ∧ s = 4, ()) ?step)
  case step =>
    intro hd tl x
    apply xwp_lemma
    simp
    intro s hinv
    split
    · simp [ExceptT.throw_spec, hinv]
    · simp only [PredTrans.pure_apply]; omega
  dsimp
  constructor
  · subst hs; conv in (List.sum _) => { whnf }; simp
  · simp; intro _ _ h; omega

theorem test_3 : ⦃True⦄ (do let mut x := 0; for i in [1:5] do { x := x + i }; pure (f := Idd) (); return x) ⦃⇓r | r < 30⦄ := by
  xwp
  xapp (Triple.forIn_list (PostCond.total fun (xs, r) => (∀ x, x ∈ xs → x ≤ 5) ∧ r + xs.length * 5 ≤ 25) ?step)
  case step =>
    simp
    intro hd tl b
    xwp hinv _ _
    omega
  simp
  constructor <;> (try (repeat intro); omega)

-- TBD: Figure out while loops
theorem test_4 : ⦃True⦄ (do let mut x := 0; let mut i := 0; while i < 4 do { x := x + i; i := i + 1 }; pure (f := Idd) (); return x) ⦃⇓r | r = 6⦄ := by
  open LawfulMonadTriple in
  simp
  sorry

theorem test_1 : ⦃True⦄ (do let mut id := 5; id := 3; pure (f := Idd) id) ⦃⇓r | r = 3⦄ := by
  refine xwp_lemma ?_
  simp

theorem test_2 : ⦃True⦄ (do let mut x := 5; if x > 1 then { x := 1 } else { x := x }; pure (f:=Idd) x) ⦃⇓r | r = 1⦄ := by
  refine xwp_lemma ?_
  simp

theorem test_2_2 : ⦃True⦄ (do let mut id := 5; id := 3; pure (f := Idd) id) ⦃⇓r | r < 20⦄ := by
  refine xwp_lemma ?_
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
    apply Idd.by_wp (fun r => SimpleGraph.dist r u v ≤ 2*t-1)
    simp
    apply triple_to_wp (ps := .pure) (Triple.foldlM_list (PostCond.total fun (xs, f_H) => ∀ i j, f_H i j → 2*t-1 < _root_.dist f_H s(i,j)) ?hstep)
    case hstep =>
      intro e es f_H
      apply xwp_lemma
      simp
      intro hinv
      if h : 2*t-1 < _root_.dist f_H e
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
  apply Idd.by_wp (· = fib_spec n)
  if h : n = 0 then simp[h,fib_spec] else ?_
  simp [h,fib_spec]
  xapp Triple.forIn_list ?inv ?step
  case inv => exact PostCond.total fun (xs, ⟨a, b⟩) => let i := n - xs.length; xs.length < n ∧ a = fib_spec (i-1) ∧ b = fib_spec i
  case step =>
    intro hd tl ⟨a, b⟩
    apply xwp_lemma
    intro ⟨htl, ha, hb⟩
    simp_all
    use Nat.lt_of_succ_lt htl
    simp_arith[Nat.succ_le_of_lt, Nat.zero_lt_of_ne_zero h, Nat.sub_sub_eq_min, Nat.sub_sub, Nat.lt_of_succ_lt] at *
    refine (fib_spec_rec ?_).symm
    simp_arith[Nat.le_sub_of_add_le' htl]
  simp_arith [Nat.succ_le_of_lt, Nat.zero_lt_of_ne_zero h, Nat.sub_sub_eq_min]
  intro y
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
  apply xwp_lemma
  simp[addRandomEvens]
  xapp (Triple.foldlM_list (PostCond.total fun (xs, r) => r % 2 = k % 2) ?step)
  case step =>
    intro hd tl b
    xwp hinv
    xapp IO.rand_spec
    simp
    intro _ _; trivial
  simp

/-- Since we're adding even numbers to our number twice, and summing,
the entire result is even. -/
theorem program_spec (n k) : ⦃True⦄ program n k ⦃⇓r | r % 2 = 0⦄ := by
  -- unfold program
  simp[program] -- only [program, bind_pure_comp, Observation.bind_bind, Observation.map_map]
  xwp
  xapp (addRandomEvens_spec n k); simp; intro r₁ h₁
  xapp (addRandomEvens_spec n k); simp; intro r₂ h₂
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
