import Mathlib.Order.CompleteLattice
import MPL.MonadMorphism

namespace MPL

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
example : PostCond α (.except ε₂ (.arg σ₂ (.except ε₁ (.arg σ₁ .pure)))) = ((α → σ₂ → σ₁ → Prop) × (ε₂ → σ₂ → σ₁ → Prop) × (ε₁ → σ₁ → Prop) × Unit) := rfl

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

instance : Inhabited (PreCond ps) where
  default := PreCond.pure True

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
noncomputable instance PreCond.instTop {ps : PredShape} : Top (PreCond ps) := inferInstance
noncomputable instance PreCond.instBot {ps : PredShape} : Bot (PreCond ps) := inferInstance

theorem PreCond.le_ext {ps} {p q : α → PreCond ps} : p ≤ q ↔ ∀ a, p a ≤ q a := ⟨fun h => h, fun h => h⟩

@[simp]
theorem PreCond.le_pure_pure {ps} {p q : Prop} : @PreCond.pure ps p ≤ @PreCond.pure ps q ↔ p ≤ q := by
  induction ps
  case pure => simp
  case arg σ s ih => sorry
  case except ε s ih => sorry

@[simp]
theorem PreCond.ext_pure_pure {ps} {p q : Prop} : @PreCond.pure ps p = @PreCond.pure ps q ↔ p = q := by
  induction ps
  case pure => simp
  case arg σ s ih => sorry
  case except ε s ih => sorry

theorem PreCond.imp_pure_extract_l {ps} {P : Prop} {P' : PreCond ps} {Q : PreCond ps}
  (h : P → P' ≤ Q) : PreCond.pure P ⊓ P' ≤ Q := by
  induction ps
  case pure => intro ⟨hp, hp'⟩; exact h hp hp'
  case arg σ s ih => intro s; apply ih (fun hp => h hp s)
  case except ε s ih => simp; apply ih h

theorem PreCond.imp_pure_extract_r {ps} {P : Prop} {P' : PreCond ps} {Q : PreCond ps}
  (h : P → P' ≤ Q) : P' ⊓ PreCond.pure P ≤ Q := by
  induction ps
  case pure => intro ⟨hp, hp'⟩; exact h hp' hp
  case arg σ s ih => intro s; apply ih (fun hp => h hp s)
  case except ε s ih => simp; apply ih h

theorem PreCond.imp_pure_extract {ps} {P : Prop} {Q : PreCond ps}
  (h : P → PreCond.pure True ≤ Q) : PreCond.pure P ≤ Q := by
  induction ps
  case pure => intro hp; exact (h hp) .intro
  case arg σ s ih => intro s; apply ih (fun hp => h hp s)
  case except ε s ih => simp; apply ih h

@[reducible]
def FailConds.const {ps : PredShape} (p : Prop) : FailConds ps := match ps with
  | .pure => ()
  | .arg σ s => @FailConds.const s p
  | .except ε s => (fun _ε => PreCond.pure p, @FailConds.const s p)

def FailConds.true : FailConds ps := FailConds.const True
def FailConds.false : FailConds ps := FailConds.const False

instance : Inhabited (FailConds ps) where
  default := FailConds.true

noncomputable instance FailConds.instLattice : {ps : PredShape} → CompleteLattice (FailConds ps)
  | .pure => ((inferInstance : CompleteLattice Unit) : CompleteLattice (FailConds .pure))
  | .arg σ s => let _ := @instLattice s; (inferInstance : CompleteLattice (FailConds s))
  | .except ε s => let _ := @instLattice s; (inferInstance : CompleteLattice ((ε → PreCond s) × FailConds s))

-- noncomputable instance FailConds.instLE {ps : PredShape} : LE (FailConds ps) := FailConds.instLattice.toLE
noncomputable instance PostCond.instPreorder : {ps : PredShape} → Preorder (PostCond α ps) := inferInstance
noncomputable instance PostCond.instLE {ps : PredShape} : LE (PostCond α ps) := inferInstance

--attribute [grind =] Prod.le_def Pi.le_def -- le_Prop_eq -- pointfree defn of le_Prop_eq not supported
--@[grind =]
--lemma le_Prop_eq_pointful {p q : Prop} : p ≤ q ↔ p → q := by rfl
--@[grind =]
--lemma PreCond.le_pure_intro {p q : PreCond .pure} : LE.le (α:=PreCond .pure) (self := PreCond.instLattice.toLE) p q ↔ p → q := by rfl
-- @[grind =]
-- lemma PreCond.le_arg_intro {p q : PreCond (.arg σ ps)} : p ≤ q ↔ (∀ s, p s ≤ q s) := by rfl
-- not sure if the following even does anything:
--@[grind =]
--lemma PreCond.le_except_intro {p q : PreCond (.except ε ps)} : p ≤ q ↔ LE.le (α := PreCond ps) p q := by rfl

@[simp]
lemma PreCond.bot_le {x : PreCond ps} : pure False ≤ x := by
  induction ps
  case pure => exact False.elim
  case arg σ s ih => intro; exact ih
  case except ε s ih => exact ih

@[simp]
lemma PreCond.pure_true_top {ps : PredShape} : PreCond.pure True = @Top.top (PreCond ps) PreCond.instTop := by
  induction ps
  case pure => rfl
  case arg σ s ih => ext; exact ih
  case except ε s ih => exact ih

@[simp]
lemma PreCond.pure_false_bot {ps : PredShape} : PreCond.pure False = @Bot.bot (PreCond ps) PreCond.instBot := by
  induction ps
  case pure => rfl
  case arg σ s ih => ext; exact ih
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

instance : Inhabited (PostCond α ps) where
  default := PostCond.total (fun _ => default)

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

def PredTrans.Mono {ps : PredShape} {α : Type} (x : PostCond α ps → PreCond ps) : Prop :=
  ∀ Q₁ Q₂, Q₁ ≤ Q₂ → x Q₁ ≤ x Q₂

@[ext]
structure PredTrans (ps : PredShape) (α : Type) : Type where
  apply : PostCond α ps → PreCond ps
  mono : PredTrans.Mono apply

--infix:100 " ⇐ " => PredTrans.apply

def PredTrans.const {ps : PredShape} {α : Type} (p : PreCond ps) : PredTrans ps α :=
  ⟨fun _ => p, fun _ _ _ => le_rfl⟩

def PredTrans.le {ps : PredShape} {α : Type} (x y : PredTrans ps α) : Prop :=
  y.apply ≤ x.apply -- the weaker the precondition, the smaller the PredTrans
def PredTrans.top {ps : PredShape} {α : Type} : PredTrans ps α :=
  PredTrans.const (PreCond.pure False)
def PredTrans.bot {ps : PredShape} {α : Type} : PredTrans ps α :=
  PredTrans.const (PreCond.pure True)
noncomputable def PredTrans.sup {ps : PredShape} {α : Type} : PredTrans ps α → PredTrans ps α → PredTrans ps α :=
  fun x y => PredTrans.mk (x.apply ⊔ y.apply) sorry
noncomputable def PredTrans.inf {ps : PredShape} {α : Type} : PredTrans ps α → PredTrans ps α → PredTrans ps α :=
  fun x y => PredTrans.mk (x.apply ⊓ y.apply) sorry
noncomputable def PredTrans.sSup {ps : PredShape} {α : Type} : Set (PredTrans ps α) → PredTrans ps α :=
  fun x => PredTrans.mk (InfSet.sInf { PredTrans.apply p | p ∈ x }) sorry
noncomputable def PredTrans.sInf {ps : PredShape} {α : Type} : Set (PredTrans ps α) → PredTrans ps α :=
  fun x => PredTrans.mk (SupSet.sSup { PredTrans.apply p | p ∈ x }) sorry

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

def PredTrans.pure {ps : PredShape} {α : Type} (a : α) : PredTrans ps α :=
  { apply := fun Q => Q.1 a, mono := by intro _ _ h; apply h.1 }

def PredTrans.bind {ps : PredShape} {α β : Type} (x : PredTrans ps α) (f : α → PredTrans ps β) : PredTrans ps β :=
  { apply := fun Q => x.apply (fun a => (f a).apply Q, Q.2), mono := by
      intro Q₁ Q₂ h
      simp only [apply]
      apply x.mono
      simp[h.2]
      intro a
      apply (f a).mono
      exact h }

instance : Monad (PredTrans ps) where
  pure := PredTrans.pure
  bind := PredTrans.bind

@[simp]
theorem PredTrans.pure_apply {ps : PredShape} {α : Type} (a : α) (Q : PostCond α ps) :
  (Pure.pure a : PredTrans ps α).apply Q = Q.1 a := by rfl

@[simp]
theorem PredTrans.map_apply {ps : PredShape} {α β : Type} (f : α → β) (x : PredTrans ps α) (Q : PostCond β ps) :
  (f <$> x).apply Q = x.apply (fun a => Q.1 (f a), Q.2) := by rfl

@[simp]
theorem PredTrans.bind_apply {ps : PredShape} {α β : Type} (x : PredTrans ps α) (f : α → PredTrans ps β) (Q : PostCond β ps) :
  (x >>= f).apply Q = x.apply (fun a => (f a).apply Q, Q.2) := by rfl

@[simp]
theorem PredTrans.seq_apply {ps : PredShape} {α β : Type} (f : PredTrans ps (α → β)) (x : PredTrans ps α) (Q : PostCond β ps) :
  (f <*> x).apply Q = f.apply (fun g => x.apply (fun a => Q.1 (g a), Q.2), Q.2) := by rfl

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

def PredTrans.get {ps : PredShape} {σ : Type} : PredTrans (.arg σ ps) σ :=
  { apply := fun Q s => Q.1 s s, mono := by
      intro Q₁ Q₂ h
      simp only [apply]
      intro s
      exact h.1 s s }

def PredTrans.set {ps : PredShape} {σ : Type} (s : σ) : PredTrans (.arg σ ps) PUnit :=
  { apply := fun Q _ => Q.1 ⟨⟩ s, mono := by
      intro Q₁ Q₂ h
      simp only [apply]
      intro _
      exact h.1 ⟨⟩ s }

def PredTrans.throw {ps : PredShape} {ε : Type} (e : ε) : PredTrans (.except ε ps) α :=
  { apply := fun Q => Q.2.1 e, mono := by
      intro Q₁ Q₂ h
      simp only [apply]
      exact h.2.1 e }

def PredTrans.tryCatch {ps : PredShape} {ε : Type} (x : PredTrans (.except ε ps) α) (handle : ε → PredTrans (.except ε ps) α) : PredTrans (.except ε ps) α :=
  { apply := fun Q => x.apply (Q.1, fun e => (handle e).apply Q, Q.2.2), mono := by
      intro Q₁ Q₂ h
      apply x.mono
      use h.1, ?_, h.2.2
      intro e
      apply (handle e).mono _ _ h }

@[simp]
def PredTrans.modify {ps : PredShape} {σ : Type} (f : σ → σ) : PredTrans (.arg σ ps) PUnit := do
  let s ← PredTrans.get
  PredTrans.set (f s)

-- The interpretation of `StateT σ (PredTrans ps) α` into `PredTrans (.arg σ ps) α`.
-- Think: modifyGetM
def PredTrans.pushArg {ps : PredShape} {σ : Type} {α : Type} (x : StateT σ (PredTrans ps) α) : PredTrans (.arg σ ps) α :=
  { apply := fun Q s => (x s).apply (fun (a, s) => Q.1 a s, Q.2), mono := by
      intro Q₁ Q₂ h
      simp only [apply]
      intro s
      apply (x s).mono
      exact ⟨fun p => h.1 p.1 p.2, h.2⟩ }

def PredTrans.popArg {ps : PredShape} {α} (x : PredTrans (.arg σ ps) α) : StateT σ (PredTrans ps) α := fun s =>
  { apply Q := x.apply (fun r s' => Q.1 (r, s'), Q.2) s,
    mono := by
      intro Q₁ Q₂ h
      apply x.mono
      simp[h.2]
      intro r s'
      apply h.1 }

-- The interpretation of `ExceptT ε (PredTrans ps) α` into `PredTrans (.except ε ps) α`
def PredTrans.pushExcept {ps : PredShape} {α ε} (x : ExceptT ε (PredTrans ps) α) : PredTrans (.except ε ps) α :=
  { apply Q := x.apply (fun | .ok a => Q.1 a | .error e => Q.2.1 e, Q.2.2),
    mono := by
      intro Q₁ Q₂ h
      apply x.mono
      simp
      exact ⟨fun | .ok a => h.1 a | .error e => h.2.1 e, h.2.2⟩ }

def PredTrans.popExcept {ps : PredShape} {α} (x : PredTrans (.except ε ps) α) : ExceptT ε (PredTrans ps) α :=
  { apply Q := x.apply (fun a => Q.1 (.ok a), fun e => Q.1 (.error e), Q.2),
    mono := by
      intro Q₁ Q₂ h
      apply x.mono
      exact ⟨fun a => h.1 (.ok a), fun e => h.1 (.error e), h.2⟩ }

def PredTrans.modifyGet {ps : PredShape} {σ : Type} {α : Type} (f : σ → α × σ) : PredTrans (.arg σ ps) α :=
  pushArg (fun a => pure (f a))

@[simp]
theorem PredTrans.modifyGet_pure {ps : PredShape} {σ : Type} {α : Type} (a : α) :
  PredTrans.modifyGet (ps:=ps) (σ:=σ) (fun s => (a, s)) = Pure.pure a := rfl

def PredTrans.withReader {ps : PredShape} {σ : Type} (f : σ → σ) (x : PredTrans (.arg σ ps) α) : PredTrans (.arg σ ps) α :=
  PredTrans.pushArg fun r => do let (a, _) ← PredTrans.popArg x (f r); Pure.pure (a, r)

lemma PredTrans.withReader_mono {ps : PredShape} {σ : Type} (f : σ → σ) (x x' : PredTrans (.arg σ ps) α) :
  x ≤ x' → withReader f x ≤ withReader f x' := by intro h Q r; apply h

instance PredTrans.instMonadLiftArg : MonadLift (PredTrans m) (PredTrans (.arg σ m)) where
  monadLift x := PredTrans.pushArg (StateT.lift x)

instance PredTrans.instMonadLiftExcept : MonadLift (PredTrans m) (PredTrans (.except ε m)) where
  monadLift x := PredTrans.pushExcept (ExceptT.lift x)

instance PredTrans.instMonadFunctorArg : MonadFunctor (PredTrans m) (PredTrans (.arg σ m)) where
  monadMap f x := PredTrans.pushArg (fun s => f (PredTrans.popArg x s))

instance PredTrans.instMonadFunctorExcept : MonadFunctor (PredTrans m) (PredTrans (.except ε m)) where
  monadMap f x := PredTrans.pushExcept (f x.popExcept)

@[simp]
def PredTrans.get_apply {ps} {σ : Type} {Q : PostCond σ (.arg σ ps)} :
  PredTrans.get.apply Q = fun s => Q.1 s s := rfl

@[simp]
def PredTrans.set_apply {ps} {σ : Type} {Q : PostCond PUnit (.arg σ ps)} (s : σ) :
  (PredTrans.set s).apply Q = fun _ => Q.1 ⟨⟩ s := rfl

@[simp]
def PredTrans.modifyGet_apply {ps} {α : Type} {σ : Type} {Q : PostCond α (.arg σ ps)} (f : σ → α × σ) :
  (PredTrans.modifyGet f).apply Q = fun s => let ⟨a, s⟩ := f s; Q.1 a s := rfl

@[simp]
def PredTrans.pushArg_apply {ps} {α : Type} {σ : Type} {Q : PostCond α (.arg σ ps)} (f : σ → PredTrans ps (α × σ)) :
  (PredTrans.pushArg f).apply Q = fun s => (f s).apply (fun ⟨a, s⟩ => Q.1 a s, Q.2) := rfl

@[simp]
def PredTrans.throw_apply {ps} {α ε : Type} {Q : PostCond α (.except ε ps)} (e : ε) :
  (PredTrans.throw e).apply Q = Q.2.1 e := rfl

@[simp]
def PredTrans.pushExcept_apply {ps} {α ε} {Q : PostCond α (.except ε ps)} (x : PredTrans ps (Except ε α)) :
  (PredTrans.pushExcept x).apply Q = x.apply (fun | .ok a => Q.1 a | .error e => Q.2.1 e, Q.2.2) := rfl

@[simp]
def PredTrans.dite_apply {ps} {Q : PostCond α ps} (c : Prop) [Decidable c] (t : c → PredTrans ps α) (e : ¬ c → PredTrans ps α) :
  (if h : c then t h else e h).apply Q = if h : c then (t h).apply Q else (e h).apply Q := by split <;> rfl

@[simp]
def PredTrans.ite_apply {ps} {Q : PostCond α ps} (c : Prop) [Decidable c] (t : PredTrans ps α) (e : PredTrans ps α) :
  (if c then t else e).apply Q = if c then t.apply Q else e.apply Q := by split <;> rfl

@[simp]
def PredTrans.monadLiftArg_apply {ps} {Q : PostCond α (.arg σ ps)} (t : PredTrans ps α) :
  (MonadLift.monadLift t : PredTrans (.arg σ ps) α).apply Q = fun s => t.apply (fun a => Q.1 a s, Q.2) := rfl

@[simp]
def PredTrans.monadLiftExcept_apply {ps} {Q : PostCond α (.except ε ps)} (t : PredTrans ps α) :
  (MonadLift.monadLift t : PredTrans (.except ε ps) α).apply Q = t.apply (fun a => Q.1 a, Q.2.2) := rfl

@[simp]
def PredTrans.monadMapArg_apply {ps} {Q : PostCond α (.arg σ ps)} (f : ∀{β}, PredTrans ps β → PredTrans ps β) (t : PredTrans (.arg σ ps) α) :
  (MonadFunctor.monadMap (m:=PredTrans ps) f t).apply Q = fun s => (f (t.popArg s)).apply (fun (a, s) => Q.1 a s, Q.2) := rfl

@[simp]
def PredTrans.monadMapExcept_apply {ps} {Q : PostCond α (.except ε ps)} (f : ∀{β}, PredTrans ps β → PredTrans ps β) (t : PredTrans (.except ε ps) α) :
  (MonadFunctor.monadMap (m:=PredTrans ps) f t).apply Q = (f t.popExcept).apply (fun | .ok a => Q.1 a | .error e => Q.2.1 e, Q.2.2) := rfl

@[simp]
def PredTrans.popArg_apply {ps} {Q : PostCond (α × σ) ps} (t : PredTrans (.arg σ ps) α) :
  (t.popArg s).apply Q = t.apply (fun a s => Q.1 (a, s), Q.2) s := rfl

@[simp]
def PredTrans.popExcept_apply {ps} {Q : PostCond (Except ε α) ps} (t : PredTrans (.except ε ps) α) :
  (t.popExcept).apply Q = t.apply (fun a => Q.1 (.ok a), fun e => Q.1 (.error e), Q.2) := rfl

@[simp]
def PredTrans.withReader_apply {ps} {Q : PostCond α (.arg ρ ps)} (f : ρ → ρ) (t : PredTrans (.arg ρ ps) α) :
  (PredTrans.withReader f t).apply Q = fun r => t.apply (fun a _ => Q.1 a r, Q.2) (f r) := rfl

instance PredTrans.instMonadMorphismPushArg : MonadMorphism (StateT σ (PredTrans ps)) (PredTrans (.arg σ ps)) (PredTrans.pushArg) where
  pure_pure := by intros; rfl
  bind_bind := by intros; rfl

instance PredTrans.instMonadMorphismPopArg : MonadMorphism (PredTrans (.arg σ ps)) (StateT σ (PredTrans ps)) (PredTrans.popArg) where
  pure_pure := by intros; rfl
  bind_bind := by intros; rfl

-- instance PredTrans.instMonadMorphismWithReader (f : ρ → ρ) : MonadMorphism (PredTrans (.arg ρ ps)) (PredTrans (.arg ρ ps)) (PredTrans.withReader f) where
--   pure_pure := by intros; rfl
--   bind_bind x k := by
--     have key : ∀ r, x.popArg r = (·.1, r) <$> x.popArg r := sorry -- A property of the range of wp at ReaderT...
--     replace key : ∀ Q r, x.apply Q r = x.apply (fun a _ => Q.1 a r, Q.2) r := sorry -- same fact, more easily applicable
--     ext Q r
--     simp[withReader, key]

-- TODO: Figure out whether the following instances are useful (I don't think they are.)
/-
instance PredTrans.instLiftMonadMorphismArg : MonadMorphism (PredTrans ps) (PredTrans (.arg σ ps)) MonadLift.monadLift where
  pure_pure x := by ext; simp only [monadLiftArg_apply, pure_apply]
  bind_bind x f := by ext Q σ; simp only [Bind.bind, bind, monadLiftArg_apply]

instance PredTrans.instLiftMonadMorphismDropFail : MonadMorphism (PredTrans ps) (PredTrans (.except ε ps)) MonadLift.monadLift where
  pure_pure x := by ext; simp only [monadLiftExcept_apply, pure_apply]
  bind_bind x f := by ext Q; simp only [Bind.bind, bind, monadLiftExcept_apply]
-/

@[simp]
theorem PredTrans.pushArg_popArg : pushArg (popArg x) = x := rfl

@[simp]
theorem PredTrans.popArg_pushArg : popArg (pushArg f) = f := rfl

-- Just a reminder for me that the following would not hold for a suitable defn of pushReader and popReader:
--theorem PredTrans.pushReader_popReader : pushReader (popReader x) = x := sorry
--  goal: x.apply (fun a x => Q.1 a x✝, Q.2) x✝ = x.apply Q x✝

instance PredTrans.instMonadMorphismPushExcept : MonadMorphism (ExceptT ε (PredTrans ps)) (PredTrans (.except ε ps)) (PredTrans.pushExcept) where
  pure_pure := by intros; rfl
  bind_bind := by
    intro _ _ x f
    ext Q
    simp only [pushExcept, Bind.bind, ExceptT.bind, ExceptT.mk, bind, ExceptT.bindCont]
    congr
    ext x
    cases x <;> simp

instance PredTrans.instMonadMorphismPopExcept : MonadMorphism (PredTrans (.except ε ps)) (ExceptT ε (PredTrans ps)) (PredTrans.popExcept) where
  pure_pure := by intros; rfl
  bind_bind := by intros; rfl

@[simp]
theorem PredTrans.pushExcept_popExcept : pushExcept (popExcept x) = x := rfl

@[simp]
theorem PredTrans.popExcept_pushExcept : popExcept (pushExcept x) = x := by
  ext Q
  simp only [ExceptT.run, popExcept, pushExcept]
  congr
  ext x
  cases x <;> simp

-- noncomputable def PredTrans.prePost {ps : PredShape} {α : Type} (P : PreCond ps) (Q : PostCond α ps) : PredTrans ps α :=
--   { apply := fun Q' => P ⊓ PreCond.pure (Q ≤ Q'), mono := by
--       intro Q₁ Q₂ h
--       simp only [apply, le_inf_iff, inf_le_left, true_and]
--       refine inf_le_of_right_le ?_
--       simp only [PreCond.le_pure_pure]
--       exact (le_trans · h) }
--
-- noncomputable def PredTrans.post {ps : PredShape} {α : Type} (Q : PostCond α ps) : PredTrans ps α :=
--   { apply := fun Q' => PreCond.pure (Q ≤ Q'), mono := by
--       intro Q₁ Q₂ h
--       simp only [apply, le_inf_iff, inf_le_left, true_and]
--       simp only [PreCond.le_pure_pure]
--       exact (le_trans · h) }
--
-- theorem PredTrans.prePost_apply {ps : PredShape} {α : Type} {P : PreCond ps} {Q : PostCond α ps} :
--   P ≤ (PredTrans.prePost P Q).apply Q := by simp[PredTrans.prePost]
--
-- theorem PredTrans.prePost_apply_conseq {ps : PredShape} {α : Type} {P : PreCond ps} {Q Q' : PostCond α ps}
--   (hpost : Q ≤ Q') :
--   P ≤ (PredTrans.prePost P Q).apply Q' := le_trans PredTrans.prePost_apply ((PredTrans.prePost P Q).mono _ _ hpost)
--
-- theorem PredTrans.le_prePost {ps : PredShape} {α : Type} {P : PreCond ps} {Q : PostCond α ps} {x : PredTrans ps α} :
--   P ≤ x.apply Q ↔ x ≤ PredTrans.prePost P Q := by
--     constructor
--     · intro h;
--       simp[PredTrans.prePost]
--       intro Q₂
--       simp
--       apply PreCond.imp_pure_extract_r
--       intro hq
--       exact le_trans h (x.mono Q Q₂ hq)
--     · intro h
--       apply le_trans PredTrans.prePost_apply (h Q)
--
