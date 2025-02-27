import Lean
import Mathlib







namespace Test

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

instance : CompleteLattice (PreCond ps) := sorry
instance : CompleteLattice (FailConds ps) := sorry
instance : CompleteLattice (PostCond α ps) := sorry

section PostCondExamples
open PredShape

variable (α ρ ε ε₁ ε₂ σ σ₁ σ₂ : Type)
#reduce (types:=true) PreCond (except ε₂ (arg σ₂ (except ε₁ (arg σ₁ pure))))
#reduce (types:=true) PostCond α (except ε₂ (arg σ₂ (except ε₁ (arg σ₁ pure))))
example : PostCond α (arg ρ pure) = ((α → ρ → Prop) × Unit) := rfl
example : PostCond α (except ε pure) = ((α → Prop) × (ε → Prop) × Unit) := rfl
example : PostCond α (arg σ (except ε pure)) = ((α → σ → Prop) × (ε → Prop) × Unit) := rfl
example : PostCond α (except ε (arg σ₁ pure)) = ((α → σ₁ → Prop) × (ε → σ₁ → Prop) × Unit) := rfl
example : PostCond α (arg σ₂ (except ε (arg σ₁ pure))) = ((α → σ₂ → σ₁ → Prop) × (ε → σ₁ → Prop) × Unit) := rfl
example : PostCond α (except ε₂ (arg σ₂ (except ε₁ (arg σ₁ pure)))) = ((α → σ₂ → σ₁ → Prop) × (ε₂ → σ₂ → σ₁ → Prop) × (ε₁ → σ₁ → Prop) × Unit) := rfl

end PostCondExamples


structure PredTrans (ps : PredShape) (α : Type) : Type where
  apply : PostCond α ps → PreCond ps
instance : Monad (PredTrans ps) := sorry

class WP (m : Type → Type) (ps : outParam PredShape) where
  wp {α} (x : m α) : PredTrans ps α
  wp_mono {α} (x : m α) (Q₁ Q₂ : PostCond α ps) :
    Q₁ ≤ Q₂ → (wp x).apply Q₁ ≤ (wp x).apply Q₂
open WP

class LawfulWP (m : Type → Type) (ps : outParam PredShape) [Monad m] [WP m ps] where
  wp_pure {α} (a : α) :
    wp (m:=m) (pure a) = pure a
  wp_bind {α β} (x : m α) (f : α → m β) :
    wp (do let a ← x; f a) = do let a ← wp x; wp (f a)

def triple {m : Type → Type} {ps : PredShape} [WP m ps] {α} (x : m α) (P : PreCond ps) (Q : PostCond α ps) : Prop :=
  P ≤ (wp x).apply Q

notation:lead "⦃" P "⦄ " x:lead " ⦃" Q "⦄" =>
  triple x P Q
notation:lead "⦃" P "⦄ " x:lead " ⦃⇓" v " | " Q "⦄" =>
  ⦃P⦄ x ⦃PostCond.total fun v => Q⦄
notation:lead "⟦" e "⟧" =>
  WP.wp e

end Test








open MPL

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
--  apply PredTrans.bind_mono (ps := .except Nat (.arg Nat .pure))
--  apply wp_apply_triple
--  apply Specs.forIn_list

  xapp (Specs.forIn_list (fun (xs, r) s => r ≤ 4 ∧ s = 4 ∧ r + xs.sum > 4, fun e s => e = 42 ∧ s = 4, ()) ?step)
  case step =>
    intro hd tl x
    xwp s hinv
    split
    · simp[hinv]
    · simp only [PredTrans.pure_apply]; omega
  dsimp
  constructor
  · subst hs; conv in (List.sum _) => { whnf }; simp
  · simp; intro _ _ h; omega

theorem test_3 : ⦃True⦄ (do let mut x := 0; for i in [1:5] do { x := x + i }; pure (f := Idd) (); return x) ⦃⇓r | r < 30⦄ := by
  xwp
  xapp (Specs.forIn_list (PostCond.total fun (xs, r) => (∀ x, x ∈ xs → x ≤ 5) ∧ r + xs.length * 5 ≤ 25) ?step)
  case step =>
    simp
    intro hd tl b
    xwp hinv _ _
    omega
  simp
  constructor <;> (try (repeat intro); omega)

def recfun : Nat → StateT Nat Idd Nat
| 0 => pure 0
| n+1 => do return (← get) + (← recfun n)

@[simp]
def recfun_spec : Nat → PredTrans (.arg Nat .pure) Nat
| 0 => pure 0
| n+1 => do return (← WP.wp (get : StateT Nat Idd Nat)) + (← recfun_spec n)

theorem wp_recfun : WP.wp (recfun n) = recfun_spec n := by
  induction n with
  | zero => simp [recfun, recfun_spec]
  | succ n ih => simp [recfun, recfun_spec, ih]

theorem test_rec :
  ⦃PreCond.pure True⦄
  recfun n
  ⦃⇓r | fun s => r = s * n⦄ := by
  induction n with
  | zero => sorry
  | succ n ih =>
    xwp
    intro s h
    revert h s
    induction n with
    | zero => simp[recfun]
    | succ n ih => simp[recfun]; xapp (ih : ⦃· = s⦄ recfun n ⦃⇓r | fun s => r = s * n⦄)
      simp
      rw[wp_recfun]
      simp +arith
      rw[ih]
      simp +arith

-- TBD: Figure out while loops
theorem test_4 : ⦃True⦄ (do let mut x := 0; let mut i := 0; while i < 4 do { x := x + i; i := i + 1 }; pure (f := Idd) (); return x) ⦃⇓r | r = 6⦄ := by
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
    apply wp_apply_triple (ps := .pure) (Specs.foldlM_list (PostCond.total fun (xs, f_H) => ∀ i j, f_H i j → 2*t-1 < _root_.dist f_H s(i,j)) ?hstep)
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
  xapp Specs.forIn_list ?inv ?step
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
  xapp (Specs.foldlM_list (PostCond.total fun (xs, r) => r % 2 = k % 2) ?step)
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
