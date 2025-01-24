-- This module serves as the root of the `Play` library.
-- Import modules here that should be built as part of the library.
import Play.Basic

import Lean
import Mathlib
import Mathlib.CategoryTheory.NatTrans

open Lean
open Lean.Parser
open Lean.Elab.Command
open Lean.Elab
open Lean.Elab.Tactic
open Lean.Meta
open Lean.SubExpr
--open Std.Range

def PredTrans.mono {α} (t : (α → Prop) → Prop) : Prop :=
  ∀ p q, p ≤ q → t p → t q

def PredTrans (α : Type u) : Type u :=
  { t : (α → Prop) → Prop // PredTrans.mono t }

@[ext]
theorem PredTrans.ext {α} (x y : PredTrans α) (h : ∀ p, x.val p = y.val p) : x = y := by
  simp[PredTrans]; ext p; simp[h]

def PredTrans.le {α} (a b : PredTrans α) : Prop :=
  ∀x, a.val x ≤ b.val x
def PredTrans.bot {α} : PredTrans α :=
  ⟨fun _ => ⊥, fun _ _ _ h => h⟩
def PredTrans.top {α} : PredTrans α :=
  ⟨fun _ => ⊤, fun _ _ _ h => h⟩
def PredTrans.inf {α} (a b : PredTrans α) : PredTrans α :=
  ⟨fun x => a.val x ⊓ b.val x, fun _ _ h => And.imp (a.property _ _ h) (b.property _ _ h)⟩
def PredTrans.sup {α} (a b : PredTrans α) : PredTrans α :=
  ⟨fun x => a.val x ⊔ b.val x, fun _ _ h => Or.imp (a.property _ _ h) (b.property _ _ h)⟩
def PredTrans.sInf {α} (s : Set (PredTrans α)) : PredTrans α :=
  ⟨fun p => ∀ w ∈ s, w.val p, fun _ _ hpq h w hws => w.property _ _ hpq (h w hws)⟩
def PredTrans.sSup {α} (s : Set (PredTrans α)) : PredTrans α :=
  ⟨fun p => ∃ w ∈ s, w.val p, fun _ _ hpq => fun | ⟨w, hws, h⟩ => ⟨w, hws, w.property _ _ hpq h⟩⟩

instance : CompleteLattice (PredTrans α) where
  le := PredTrans.le
  sup := PredTrans.sup
  inf := PredTrans.inf
  bot := PredTrans.bot
  top := PredTrans.top
  sInf := PredTrans.sInf
  sSup := PredTrans.sSup
  le_refl := fun _ _ hp => hp
  le_trans := fun _ _ _ hab hbc p => (hab p).trans (hbc p)
  le_antisymm := fun _ _ hab hba => by apply PredTrans.ext; intro p; exact (hab p).antisymm (hba p)
  le_top := fun _ _ _ => .intro
  bot_le := fun _ _ fls => fls.elim
  -- and so on

def PredTrans.pure {α} (x : α) : PredTrans α :=
  ⟨fun p => p x, fun _ _ hpq ht => hpq x ht⟩
def PredTrans.bind {α β} (x : PredTrans α) (f : α → PredTrans β) : PredTrans β :=
  ⟨fun p => x.val (fun a => (f a).val p), fun _ _ hpq => x.property _ _ (fun a => (f a).property _ _ hpq)⟩

instance : Monad PredTrans where
  pure := PredTrans.pure
  bind := PredTrans.bind
instance : LawfulMonad PredTrans where
  bind_pure_comp := by intros; ext p; simp only [bind, PredTrans.bind, pure, PredTrans.pure, Functor.map, Function.comp_apply]
  pure_bind := by intros; ext p; simp only [bind, PredTrans.bind, pure, PredTrans.pure]
  bind_assoc := by intros; ext p; simp only [bind, PredTrans.bind]
  bind_map := by intros; ext p; simp only [bind, PredTrans.bind, Functor.map, Function.comp_apply, PredTrans.pure, Seq.seq]

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

@[simp]
theorem Monad.bind_unit {m : Type u → Type v} [Monad m] {x : m PUnit} {f : PUnit → m α} :
  (do let a ← x; f a) = (do x; f ⟨⟩) := by simp only

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

def SatisfiesSM {m : Type u → Type v} {α} [Monad m] (x : StateT σ m α) (p : α × σ → Prop) : Prop :=
  Subst⟦do let a ← x; let s ← get; pure (a, s)⟧ p

theorem SatisfiesSM.subst [Monad m] [LawfulMonad m] {x : StateT σ m α}
  {f g : α → StateT σ m β}
  (hp : SatisfiesSM x p) (hf : ∀ a s, p (a, s) → (do set s; f a) = (do set s; g a)) :
  x >>= f = x >>= g := by
    suffices h : (do let (a,s) ← (do let a ← x; let s ← get; pure (a, s)); set s; f a) = (do let (a,s) ← (do let a ← x; let s ← get; pure (a, s)); set s; g a) by
      simp at h
      simp[← LawfulMonad.bind_assoc] at h
      assumption
    unfold SatisfiesSM at hp
    apply hp.subst fun ⟨a, s⟩ => hf a s

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

elab "vcgen" /-("invariant " ilbls:ident ": " inv:term)*-/ : tactic => withMainContext <| do
  let goal ← getMainGoal
  let ctx ← mkSimpContext Syntax.missing (eraseLocal := false)
  try
    let goal := match ← dsimpGoal goal ctx.ctx with
    | (some goal, _) => goal
    | _              => goal
    replaceMainGoal [goal]
  catch _ => pure ()
  let mut verification_conds := #[]
  while true do
    let goal :: goals ← getGoals | break
    if ← goal.isAssigned then setGoals goals; continue
    let (_xs, goal) ← goal.intros
    let ty ← instantiateMVars (← goal.getType)
    -- ty = @Subst m α [Functor m] prog post
    if ¬(ty.isAppOfArity `Subst 5) then
      logInfo m!"give up on {ty}"
      verification_conds := verification_conds.push goal
      setGoals goals
      continue
    let prog := ty.appFn!.appArg!
    let α := ty.appFn!.appFn!.appFn!.appArg!
    let m := ty.appFn!.appFn!.appFn!.appFn!.appArg!

    -- Convention: ⟦P⟧(x) for Subst P x
    if prog.isAppOfArity ``Pure.pure 4 then
      -- prog = @pure m [Pure m] α (x : α)
      -- ⟦P⟧(pure x)
      -- <=={Satisfies.pure}
      -- P x
      let [goal] ← goal.applyConst ``Subst.pure | throwError "argh"
      replaceMainGoal [goal]
      continue
    else if prog.isAppOfArity ``Bind.bind 6 then
      -- prog = @bind m [Bind m] α β e f
      -- ⟦P⟧(bind e f)
      -- <=={Satisfies.bind}
      -- P⟦fun r => ⟦P⟧(f r)⟧(e)
      let [goal] ← goal.applyConst ``Subst.bind | throwError "argh"
      replaceMainGoal [goal]
      continue
    else if prog.isAppOfArity ``ForIn.forIn 9 then
      -- prog = @forIn {m} {ρ} {α} [ForIn m ρ α] {β} [Monad m] xs init f
      -- ⟦P⟧(forIn xs init f)
      -- <=={Subst.forIn_*} (depending on ρ)
      -- ... a bunch of sub-goals, including the invariant
      let ρ := prog.appFn!.appFn!.appFn!.appFn!.appFn!.appFn!.appFn!.appArg!;
      if ρ.isConstOf ``Std.Range then
        let goals ← goal.applyConst ``Subst.forIn_range
        replaceMainGoal goals
        continue
      else if ρ.isConstOf ``List then
        let goals ← goal.applyConst ``Subst.forIn_range
        replaceMainGoal goals
        continue
      -- let name := match
      replaceMainGoal [goal]
      continue
    else if prog.isLet then
      -- C ⊢ ⟦P⟧(do let x : ty := val; prog)
      -- <=={lift_let; intros}
      -- C; let x : ty := val ⊢ ⟦P⟧(prog)
      let ty ← instantiateMVars (← goal.getType)
      let goal ← goal.change (← ty.liftLets mkLetFVars)
      let (_xs, goal) ← goal.intros
      replaceMainGoal [goal]
      continue
    else if prog.isIte then
      -- ⟦P⟧((if b then prog₁ else prog₂))
      -- <=={split}
      -- (b → ⟦P⟧(prog₁) ∧ ((¬b) → ⟦P⟧(prog₂))
      let some (tt,ff) ← splitIfTarget? goal | throwError "wlp failed"
      replaceMainGoal [tt.mvarId, ff.mvarId]
      continue
    else if let .fvar fvarId := prog.getAppFn then -- inline locals
      -- C; let __do_jp : ty := val ⊢ ⟦P⟧(__do_jp y x))
      -- <=={dsimp only [__do_jp]}
      -- C; let __do_jp : ty := val ⊢ ⟦P⟧(val y x))
      try
        -- Why can't I test fvarId.isLetVar? here, but zeta succeeds???
        let goal ← zetaDeltaTarget goal fvarId
        replaceMainGoal [goal]
        continue
      catch _ => pure ()
    else if m.isConstOf ``Id then
      -- Id x is definitionally equal to x, and we can apply Subst.pure in that case
      -- prog = @pure m [Pure m] α (x : α)
      -- ⟦P⟧(pure x)
      -- <=={Satisfies.pure}
      -- P x
      let [goal] ← goal.applyConst ``Subst.pure | throwError "argh"
      replaceMainGoal [goal]
      continue
    else if α.isConstOf ``PUnit then
      -- If c : m PUnit, then the predicate is constant and can be pulled out
      -- ⟦P⟧(c)
      -- <=={Satisfies.split_unit}
      -- P ⟨⟩
      let [goal] ← goal.applyConst ``Subst.split_unit | throwError "argh"
      replaceMainGoal [goal]
      continue

    logInfo m!"give up on {repr prog}"
    verification_conds := verification_conds.push goal
    setGoals goals
    continue

  setGoals verification_conds.toList

theorem test_5 : Subst⟦do let mut x := 0; for i in [1:5] do { x := x + i }; pure (f := Id) (); return x⟧ (fun r => r ≤ 25) := by
  vcgen
  case inv => exact (fun xs r => (∀ x, x ∈ xs → x ≤ 5) ∧ r + xs.length * 5 ≤ 25)
  set_option trace.grind.debug true in
  case hpre => simp_all; omega
  case hweaken => simp_all
  case hdone => simp_all
  case hyield h => injection h; simp_all; omega

theorem test_6 : Subst (m:=Id) (do let mut x := 0; let mut i := 0; while i < 4 do { x := x + i; i := i + 1 } return x) (fun r => r ≤ 1) := by
  dsimp
  vcgen
  case inv => exact (fun xs r => (∀ x, x ∈ xs → x ≤ 5) ∧ r + xs.length * 5 ≤ 25)
  case hpre => simp; omega
  case hweaken => simp
  case hdone => intros; apply Subst.pure; simp;
  case hyield => intros; apply Subst.pure; simp_all; intro _ h; injection h; omega

theorem test_1 : Subst (m:=Id) (do return 3) (fun r => r = 3) := by
  vcgen
  trivial

theorem test_2 : Subst (m:=Id) (do let mut id := 5; id := 3; return id) (fun r => r = 3) := by
  vcgen
  trivial

theorem test_3 [Monad m] [LawfulMonad m] (h : Subst e₁ (fun _ => Subst (m:=m) (do e₂; e₃) P)) : Subst (m:=m) (do e₁; e₂; e₃) P := by
  vcgen
  trivial

theorem test_4 : Subst (m:=Id) (do let mut x := 5; if x > 1 then { x := 1 } else { x := x }; pure x) (fun r => r ≤ 1) := by
  vcgen <;> simp; omega

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

def greedySpanner {n:ℕ }(G : FinSimpleGraph n) (t :ℕ ): FinSimpleGraph n := Id.run do
  let mut f_H : Fin n → Fin n → Prop := fun (_ _) ↦ false
  for e in G.edgeFinset.toList do
    if (2*t -1) < dist f_H e then f_H := AddEdge f_H e
  SimpleGraph.fromRel f_H

lemma correctnessOfGreedySpanner {n:ℕ }(G : FinSimpleGraph n)(t :ℕ ) (u v : Fin n) :
  (greedySpanner G t).dist u v ≤ 2*t-1 := by
    unfold greedySpanner
    simp
    exact (Obs_Id_eq (P:=fun (r:FinSimpleGraph n) => r.dist u v ≤ 2*t-1)).mp <| by
      vcgen
end UserStory1


def fib_impl (n : Nat) := Id.run do
  if n = 0 then return 0
  let mut a := 0
  let mut b := 0
  b := b + 1
  for _ in [1:n] do
    let a' := a
    a := b
    b := a' + b
  return b

def fib_spec : Nat → Nat
| 0 => 0
| 1 => 1
| n+2 => fib_spec n + fib_spec (n+1)

theorem fib_correct {n} : fib_impl n = fib_spec n := Obs_Id_eq (P := fun r => r = fib_spec n) <| by
  vcgen
  case isTrue => simp_all[fib_spec]
  case inv => exact (fun | xs, ⟨a, b⟩ => a = fib_spec (n - xs.length - 1) ∧ b = fib_spec (n - xs.length))
  case hpre col _ h =>
    simp_all[List.range']
    have : 1 ≤ n := Nat.succ_le_of_lt (Nat.zero_lt_of_ne_zero h)
    rw[Nat.div_one, Nat.sub_one_add_one h, Nat.sub_sub, Nat.sub_add_cancel this, Nat.sub_self, Nat.sub_sub_self this]
    simp_all[fib_spec]
    exact ⟨rfl, rfl⟩
  case hweaken => apply Subst.pure; simp_all
  case hdone.hx.h.h => simp_all
  case hyield.hx.h.h b' h => injection h; subst b'; subst_vars; simp_all; rw[fib_spec] at ⊢;
  -- The default simp set eliminates the binds generated by `do` notation,
  -- and converts the `for` loop into a `List.foldl` over `List.range'`.
  simp [fib_impl, Id.run]
  match n with
  | 0 => simp [fib_spec]
  | n+1 =>
    -- Note here that we have to use `⟨x, y⟩ : MProd _ _`, because these are not `Prod` products.
    suffices ((List.range' 1 n).foldl (fun b a ↦ ⟨b.snd, b.fst + b.snd⟩) (⟨0, 1⟩ : MProd _ _)) =
        ⟨fib_spec n, fib_spec (n + 1)⟩ by simp_all
    induction n with
    | zero => rfl
    | succ n ih => simp [fib_spec, List.range'_1_concat, ih]
/-
https://lean-fro.zulipchat.com/#narrow/channel/398861-general/topic/baby.20steps.20towards.20monadic.20verification

-/

def StateT.le [base : ∀{α}, PartialOrder (w α)] : StateT σ w α → StateT σ w α → Prop :=
  fun x y => ∀s, x.run s ≤ y.run s
instance [base : ∀{α}, PartialOrder (w α)] : PartialOrder (StateT σ w α) where
  le := StateT.le
  le_refl := fun x => fun s => le_refl (x.run s)
  le_trans := fun x y z hxy hyz => fun s => (hxy s).trans (hyz s)
  le_antisymm := fun x y hxy hyx => funext fun s => (hxy s).antisymm (hyx s)

class MonadOrdered (w : Type u → Type v) [Monad w] [∀{α},Lattice (w α)] where
  -- the following theorem combines
  -- * substitutivity (x ≤ y → x >>= f ≤ y >>= f)
  -- * congruence (f ≤ g → x >>= f ≤ x >>= g)
  bind_mono : ∀{α β} (x y : w α) (f g : α → w β), x ≤ y → f ≤ g → x >>= f ≤ y >>= g

attribute [simp] MonadOrdered.bind_mono

@[simp]
theorem MonadOrdered.map_mono {α β} [Monad w] [LawfulMonad w] [∀{α},Lattice (w α)] [MonadOrdered w] (f : α → β) (x y : w α) (h : x ≤ y) : f <$> x ≤ f <$> y := by
  simp only [←bind_pure_comp]
  exact bind_mono x y (pure ∘ f) (pure ∘ f) h (by rfl)

instance PredTrans.instMonadOrdered : MonadOrdered PredTrans where
  bind_mono := by
    intros _ _ x y f g hxy hfg p hxf
    simp[Bind.bind,PredTrans.bind] at *
    apply hxy
    exact x.property (fun a => (f a).val p) _ (fun a => hfg a p) hxf

instance StateT.instMonadOrdered [Monad w] [∀{α},Lattice (w α)] [MonadOrdered w] : MonadOrdered (StateT σ w) where
  bind_mono := by
    intros _ _ _ _ _ _ hxy hfg
    intro s
    simp
    apply MonadOrdered.bind_mono
    apply hxy
    intro p;
    apply hfg

class Observation (m : Type u → Type v) (w : Type u → Type x) [Monad m] [Monad w] [∀{α}, Lattice (w α)] [MonadOrdered w] where
  observe : m α → w α
  pure_pure : observe (pure (f:=m) a) = pure (f := w) a
  bind_bind (x : m α) (f : α → m β) : observe (x >>= f) = observe x >>= (fun a => observe (f a))

instance Id.instMonadMorphismPredTrans : Observation Id PredTrans where
  observe := pure
  pure_pure := by simp
  bind_bind := by simp
instance Subst.instMonadMorphism [Monad m] [LawfulMonad m] : Observation m PredTrans where
  observe := Subst
  pure_pure := by
    intros _ a
    ext p
    constructor
    case mpr => simp[Pure.pure, PredTrans.pure]; exact Subst.pure
    case mp => sorry -- not sure if possible!
  bind_bind := by
    intros _ _ x f
    ext p
    simp
    constructor
    case mpr => sorry
    case mp => sorry
instance StateT.instMonadMorphism [Monad m] [Monad w] [base : Observation m w] : Observation (StateT σ m) (StateT σ w) where
  observe := fun x s₁ => base.observe (x.run s₁)
  pure_pure := by
    intros _ a
    ext s
    simp[StateT.run,Pure.pure,StateT.pure,base.pure_pure]
  bind_bind := by
    intros _ _ x f
    ext s
    simp[StateT.run,Bind.bind,StateT.bind,base.bind_bind]
def ExceptT.observe [Monad m] [Monad w] [base : Observation m w] (x : ExceptT ε m α) : ExceptT ε w α :=
  ExceptT.mk (base.observe (ExceptT.run x))
instance ExceptT.instMonadMorphism [Monad m] [Monad w] [base : Observation m w] : Observation (ExceptT ε m) (ExceptT ε w) where
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


theorem Tmp.forIn_list {α β} {m : Type u → Type v} {w : Type u → Type x}
    {xs : List α} {init : β} {f : α → β → Id (ForInStep β)}
    (inv : List α → PredTrans β)
    (hinv_inv : ∀ {xs}, inv xs >>= (fun _ => inv xs) = inv xs)
    (hpre : inv xs ≤ pure init)
    (hstep : ∀ {hd tl b}, (inv (hd::tl) ≤ pure b) →
        .yield <$> inv tl ≤ Observation.observe (f hd b)
      ∨ .done  <$> inv [] ≤ Observation.observe (f hd b)) :
      inv [] ≤ Observation.observe (forIn xs init f) := by
    have instMorph : Observation Id PredTrans := inferInstance
    let monotone (f : List α → PredTrans β) := ∀ xs ys, List.IsSuffix xs ys → f xs ≤ f ys
    suffices hmono : monotone fun xs => inv xs >>= fun b => Observation.observe (forIn xs b f) by
      calc inv []
        _ = inv [] >>= fun b => Observation.observe (forIn [] b f) := by simp only [List.forIn_nil, instMorph.pure_pure, bind_pure]
        _ ≤ inv xs >>= fun b => Observation.observe (forIn xs b f) := hmono [] xs (by simp)
        _ ≤ pure init >>= fun b => Observation.observe (forIn xs b f) := MonadOrdered.bind_mono _ _ _ _ hpre (by rfl)
        _ ≤ Observation.observe (forIn xs init f) := by simp

    -- intuition: inv encapsulates the effects of looping over a prefix of xs (and gets passed the suffix)
    --
    -- we need some antitonicity property; i.e. that
    --   inv xs >>= fun a => Observation.observe (forIn xs a f)
    -- decreases with when the length of xs increases.
    -- (This is because the invariant is stronger than the actual weakest precondition,
    -- and the longer the list, the more we rely on the invariant.)
    -- Then for the initial case (full xs), we have an lower bound via hpre and
    --   Observation.observe (forIn xs init f)
    -- conversely, for the final case (empty xs), we have an upper bound
    --   inv []
    -- because `forIn [] a f` is the identity.
    intro xssuff ys ⟨xspre, hsuff⟩
    induction ys
    case nil => simp_all only [List.nil_append, le_refl]
    case cons hd tl h =>
      simp_all
      simp only [List.forIn_cons, Observation.bind_bind]
      simp
      cases hstep hpre
      case inl hstep =>
        apply LE.le.trans _ (MonadOrdered.bind_mono _ _ _ _ hstep (by rfl))
        simp
        apply LE.le.trans (MonadOrdered.bind_mono _ _ _ _ (by rfl) (funext (fun a => h (sorry : pure a ≤ inv tl)))
      simp[←bind_pure_comp] --, Observation.bind_bind]
      conv in (pure _) => rw[←instMorph.pure_pure]
      conv => lhs; enter [2, a]; rw[←instMorph.bind_bind (f := fun a => pure (ForInStep.yield a))]
      simp only [←instMorph.bind_bind]
      simp[Observation.bind_bind, MonadOrdered.map_mono]
      simp[Observation.bind_bind, MonadOrdered.bind_mono]
      simp[MonadOrdered.bind_mono]
      apply MonadOrdered.bind_mono
      have : Observation.observe (f hd init) (fun | .yield b' => inv tl b' | .done b' => inv [] b') :=
        Subst.split_step (hyield hpre) (hdone hpre)
      apply Subst.mono this
      intro r hres
      match r with
      | .done b => apply Subst.pure; apply hweaken; assumption
      | .yield b => simp; simp at hres; exact @h b hres




class MonadSpec (w : Type u → Type x) [Monad w] [∀{α}, PartialOrder (w α)] where
  forIn_list {α β} {xs : List α} {init : β} {f : α → β → m (ForInStep β)} {p : α → prop}
    (inv : List α → w β)                          -- user-supplied loop invariant
    (hpre : pure init ≤ inv xs)                          -- pre⟦for {inv} xs init f⟧(p)
    (hweaken : inv [] ≤ p)               -- vc₁: weaken invariant to postcondition after loop exit
    (hdone : ∀ {hd tl b}, inv (hd::tl) b →        -- vc₂: weaken invariant to precondition of loop body upon loop entry, done case
            observe (f hd b) (∀ b', · = .done b'  → inv [] b'))
    (hyield : ∀ {hd tl b},
          (pure b ≤ inv (hd::tl) →       -- vc₃: weaken invariant to precondition of loop body upon loop entry, yield case
          pure (.yield b') ≤ inv tl)
          → observe

          (∀ b', pure (.yield b') ≤ inv tl) ≤ observe (f hd b) (∀ pure (.yield b') ∀ b', · = .yield b' → inv tl b')) :
      observe (forIn xs init f)


theorem bleh {a : α} {s : σ} : (fun p => p (a, s)) → (do s ← Subst get; Subst (Pure.pure (a, s))) := by
  intro h
  simp only [observe]
  vcgen
  assumption

theorem StateT.observe.pure {m : Type u → Type v} {p : α × σ → Prop} [Monad m] [LawfulMonad m]
  (hp : p (a, s)) : StateT.observe (m:=m) (pure a) s p := by
  simp only [observe, pure_bind, LawfulMonadState.set_get]
  vcgen
  assumption

theorem StateT.observe.get_pre {m : Type u → Type v} [Monad m] [LawfulMonad m] {p : σ × σ → Prop} (hp : p ⟨s, s⟩) :
  StateT.observe (m:=m) get s p := by
  simp only [observe, pure_bind, LawfulMonadState.set_get]
  vcgen
  assumption

theorem StateT.observe.get {m : Type u → Type v} [Monad m] [LawfulMonad m] :
  StateT.observe (m:=m) get s (· = ⟨s, s⟩) := StateT.observe.get_pre (by rfl)

theorem StateT.observe.set_pre {m : Type u → Type v} [Monad m] [LawfulMonad m] {p : PUnit × σ → Prop} (hp : p ⟨⟨⟩, s₂⟩) :
  StateT.observe (m:=m) (set s₂) s₁ p := by
  simp only [observe, pure_bind, Monad.bind_unit]
  simp only [← LawfulMonad.bind_assoc, LawfulMonadState.set_set]
  simp only [LawfulMonadState.set_get_pure]
  simp [-LawfulMonad.bind_pure_comp]
  vcgen
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
