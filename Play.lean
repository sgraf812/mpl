import Lean
import Mathlib
import MPL

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
  do
    let mut x := 0
    let s ← get
    for i in [1:s] do { x := x + i; if x > 4 then throw 42 }
    (set 1 : ExceptT Nat (StateT Nat Idd) PUnit)
    return x
  ⦃(fun r s => False,
    fun e s => e = 42 ∧ s = 4,
    ())⦄ := by
  xstart
  intro s hs
  xwp
  -- xbind -- optional
  xapp (Specs.forIn_list (fun (xs, r) s => r ≤ 4 ∧ s = 4 ∧ r + xs.sum > 4, fun e s => e = 42 ∧ s = 4, ()) ?step)
  case pre => simp only [hs]; conv in (List.sum _) => { whnf }; simp
  case step =>
    intro hd tl b
    xstart
    xwp
    simp only [List.sum_cons]
    intro b' hinv
    split
    · grind -- simp[hinv, h]
    · simp only [PredTrans.pure_apply]; grind -- omega
  simp only [List.sum_nil, add_zero]
  sgrind

theorem test_3 : ⦃True⦄ (do let mut x := 0; for i in [1:5] do { x := x + i }; pure (f := Idd) (); return x) ⦃⇓r | r < 30⦄ := by
  intro _
  xwp
  xapp (Specs.forIn_list (PostCond.total fun (xs, r) => (∀ x, x ∈ xs → x ≤ 5) ∧ r + xs.length * 5 ≤ 25) ?step)
  case pre => sgrind
  case step =>
    intro hd tl b
    xwp
    -- grind -- does not work yet... Maybe in 4.17
    simp +contextual
    omega
  sgrind

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
    apply Idd.by_wp (fun r => SimpleGraph.dist r u v ≤ 2*t-1)
    xwp
    xapp (Specs.foldlM_list (PostCond.total fun (xs, f_H) => ∀ i j, f_H i j → 2*t-1 < _root_.dist f_H s(i,j)) ?hstep)
    case hstep =>
      intro e es f_H hinv
      xwp
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
  xwp
  if h : n = 0 then simp[h,fib_spec] else ?_
  simp[h]
  xapp Specs.forIn_list ?inv ?step
  case inv => exact PostCond.total fun (xs, ⟨a, b⟩) => let i := n - xs.length; xs.length < n ∧ a = fib_spec (i-1) ∧ b = fib_spec i
  case pre => simp +arith +decide [Nat.succ_le_of_lt, Nat.zero_lt_of_ne_zero h, Nat.sub_sub_eq_min]
  case step =>
    intro hd tl ⟨a, b⟩ ⟨htl, ha, hb⟩
    xwp
    use Nat.lt_of_succ_lt htl
    simp_arith[Nat.succ_le_of_lt, Nat.zero_lt_of_ne_zero h, Nat.sub_sub_eq_min, Nat.sub_sub, Nat.lt_of_succ_lt, ha, hb] at *
    refine (fib_spec_rec ?_).symm
    simp_arith[Nat.le_sub_of_add_le' htl]
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
  unfold addRandomEvens -- TODO: integrate into xwp or xstart, make it an option
  xwp
  intro h
  xapp (Specs.foldlM_list (PostCond.total fun (xs, r) => r % 2 = k % 2) ?step)
  case step =>
    intro hd tl b hinv
    xwp
    xapp IO.rand_spec
    sgrind

/-- Since we're adding even numbers to our number twice, and summing,
the entire result is even. -/
theorem program_spec (n k) : ⦃True⦄ program n k ⦃⇓r | r % 2 = 0⦄ := by
  unfold program
  xwp
  intro h
  xapp (addRandomEvens_spec n k); intro r₁ h₁
  xapp (addRandomEvens_spec n k); intro r₂ h₂
  -- grind -- can't do it; check after 4.17 release
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
