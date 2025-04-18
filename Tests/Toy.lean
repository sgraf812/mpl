import Lean
import Mathlib
import MPL

open MPL

theorem test_sum :
  ⦃True⦄
  do
    let mut x := 0
    for i in [1:5] do
      x := x + i
    pure (f := Idd) x
  ⦃⇓r => r < 30⦄ := by
  mintro -
  mvcgen
  mspec (Specs.forIn_list (⇓ (r, xs) => (∀ x, x ∈ xs.suff → x ≤ 5) ∧ r + xs.suff.length * 5 ≤ 25) ?step)
  case step =>
    intro b pref x suff h
    mintro ⌜h₁⌝
    -- grind -- does not work yet... Maybe in 4.17
    simp_all
    omega
  all_goals simp; omega -- sgrind

def mkFreshInt [Monad m] [MonadStateOf (Nat × Nat) m] : m Nat := do
  let n ← Prod.fst <$> get
  modify (fun s => (s.1 + 1, s.2))
  pure n

private abbrev fst : SVal ((Nat × Nat)::σs) Nat := fun s => SVal.pure s.1
private abbrev snd : SVal ((Nat × Nat)::σs) Nat := fun s => SVal.pure s.2

@[spec]
theorem mkFreshInt_spec [Monad m] [LawfulMonad m] [WPMonad m sh] :
  ⦃⌜#fst = n ∧ #snd = o⌝⦄
  (mkFreshInt : StateT (Nat × Nat) m Nat)
  ⦃⇓ r => ⌜r = n ∧ #fst = n + 1 ∧ #snd = o⌝⦄ := by
  mintro _
  unfold mkFreshInt
  mvcgen
  mintro ∀s
  simp

@[wp_simp]
theorem StateT.mkFreshInt_apply [Monad m] [LawfulMonad m] [WPMonad m sh] :
  wp⟦(mkFreshInt : StateT (Nat × Nat) m Nat)⟧.apply Q = fun s => Q.1 s.1 (s.1 + 1, s.2) := by
    unfold mkFreshInt; wp_simp

@[wp_simp]
theorem MonadStateOf.mkFreshInt_apply [Monad m] [MonadStateOf (Nat × Nat) m] [Monad n] [LawfulMonad m] [LawfulMonad n] [WP m psm] [WPMonad n psn] [MonadLift m n] [MonadMorphism m n MonadLift.monadLift] :
  wp⟦mkFreshInt : n Nat⟧.apply Q = wp⟦MonadLift.monadLift (m:=m) mkFreshInt : n Nat⟧.apply Q := by
    unfold mkFreshInt; wp_simp; rfl

@[spec]
theorem mkFreshInt_lift_spec [Monad m] [LawfulMonad m] [WPMonad m sh] :
  ⦃fun _ s => ⌜s.1 = n ∧ s.2 = o⌝⦄
  (mkFreshInt : ExceptT Char (ReaderT Bool (StateT (Nat × Nat) m)) Nat)
  ⦃⇓ r _ s => ⌜r = n ∧ s.1 = n + 1 ∧ s.2 = o⌝⦄ := by
  mintro _
  mvcgen
  simp

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
  intro s hs
  xwp
  -- xbind -- optional
  xapp (Specs.forIn_list (fun (r, xs) s => r ≤ 4 ∧ s = 4 ∧ r + xs.suff.sum > 4, fun e s => e = 42 ∧ s = 4, ()) ?step)
  case pre => simp only [hs]; conv in (List.sum _) => { whnf }; simp
  case step =>
    intro b pref x suff h
    xstart
    xwp
    simp only [h, List.sum_cons]
    intro b' hinv
    split
    · grind -- simp[hinv, h]
    · simp only [PredTrans.pure_apply]; sorry -- grind -- omega
  simp only [List.sum_nil, add_zero]
  intro _ _; simp; omega -- sgrind

theorem test_ex2 :
  ⦃fun s => s = 4⦄
  do
    let mut x := 0
    let s ← get
    for i in [1:s] do { x := x + i; if x > 4 then throw x } -- NB: throw x. impossible to prove stuff about? No, could strengthen loop invariant to assert more info about x and assume that in fail cond
    (set 1 : ExceptT Nat (StateT Nat Idd) PUnit)
    return x
  ⦃(fun r s => False,
    fun e s => e > 4 ∧ s = 4,
    ())⦄ := by
  xstart
  intro s hs
  xwp
  -- xbind -- optional
  xapp (Specs.forIn_list (fun (r, xs) s => r ≤ 4 ∧ s = 4 ∧ r + xs.suff.sum > 4, fun e s => e > 4 ∧ s = 4, ()) ?step)
  case pre => simp only [hs]; conv in (List.sum _) => { whnf }; simp
  case step =>
    intro b pref x suff h
    xstart
    xwp
    simp only [h, List.sum_cons]
    intro b' hinv
    split
    · simp[hinv]; assumption
    · simp only [PredTrans.pure_apply]; sorry -- grind -- omega
  simp only [List.sum_nil, add_zero]
  sorry -- sgrind

-- theorem forIn_break_throw : forIn xs ⟨none, init⟩ f = (forIn xs init (fun x s => do match (← f x s) with | .yield )).

example :
  wp (m:= ExceptT Nat (StateT Nat (ReaderT Bool Id))) (withTheReader Bool not (do if (← read) then return 0 else return 1)) =
  wp (m:= ExceptT Nat (StateT Nat (ReaderT Bool Id))) (do if (← read) then return 1 else return 0) := by
    ext Q : 2
    xwp
    simp[ite_app]

example :
  wp (m:= ReaderT Char (StateT Bool (ExceptT Nat Id))) (do set true; throw 42; set false; get) =
  wp (m:= ReaderT Char (StateT Bool (ExceptT Nat Id))) (do set true; throw 42; get) := by
    ext Q : 2
    xwp

example :
  wp (m:= ReaderT Char (StateT Bool (ExceptT Nat Id)))
     (do try { set true; throw 42 } catch _ => set false; get) =
  wp (m:= ReaderT Char (StateT Bool (ExceptT Nat Id)))
     (do set false; get) := by
    ext Q : 2
    xwp

theorem test_loop_break :
  ⦃⌜‹Nat›ₛ = 42⌝⦄
  do
    let mut x := 0
    let s ← get
    for i in [1:s] do { x := x + i; if x > 4 then break }
    (set 1 : StateT Nat Idd PUnit)
    return x
  ⦃⇓ r => ⌜r > 4 ∧ ‹Nat›ₛ = 1⌝⦄ := by
  xstart
  intro s hs
  xwp
  -- xbind -- optional
  xapp (Specs.forIn_list (fun (r, xs) s => (r ≤ 4 ∧ r = xs.rpref.sum ∨ r > 4) ∧ s = 42, ()) ?step)
  case step =>
    intro b pref x suff h
    xwp
    simp only [h, List.sum_cons]
    intro b' hinv
    split
    · simp_all
    · simp only [PredTrans.pure_apply]; sorry -- grind -- omega
  intro r s' ⟨h, hs'⟩
  subst_vars
  (conv at h in (List.sum _) => whnf)
  simp_all
  omega

theorem get_spec [Monad m] [WPMonad m ps] {Q : PostCond σ (.arg σ ps)} :
  ⦃fun s => Q.1 s s⦄ (get : StateT σ m σ) ⦃Q⦄ := by xwp

theorem test_loop_early_return :
  ⦃fun s => s = 4⦄
  do
    let mut x := 0
    let s ← get
    for i in [1:s] do { x := x + i; if x > 4 then return 42 }
    (set 1 : StateT Nat Idd PUnit)
    return x
  ⦃⇓ r s => r = 42 ∧ s = 4⦄ := by
  xstart
  simp only [gt_iff_lt, bind_pure_comp, map_pure, Std.Range.forIn_eq_forIn_range', Std.Range.size,
    add_tsub_cancel_right, Nat.div_one, pure_bind]-- , bind_bind, MonadState.wp_get, StateT.wp_get,
    -- PredTrans.bind_apply, PredTrans.get_apply]
  intro s hs
  xapp get_spec
  xbind
  xapp (Specs.forIn_list (fun (r, xs) s => (r.1 = none ∧ r.2 = xs.rpref.sum ∧ r.2 ≤ 4 ∨ r.1 = some 42 ∧ r.2 > 4) ∧ s = 4, ()) ?step)
  case step =>
    intro b pref x suff h s ⟨h, hs⟩
    xwp
    split
    case isTrue h => simp_all[h]
    case isFalse h => simp_all[h]; omega
  intro ⟨r,x⟩ s' ⟨h, hs'⟩
  xwp
  cases r
  case none => simp[hs] at h; (conv at h in (List.sum _) => whnf); exfalso; clear s' hs' s hs; have ⟨h₁,h₂⟩ := h; subst_vars; contradiction -- omega -- WTF why doesn't omega
  case some r => simp_all

example : x = 6 ∧ x ≤ 4 → False := by intro h; omega

example : wp⟦do try { throw 42; return 1 } catch _ => return 2 : Except Nat Nat⟧ =
          wp⟦pure 2 : Except Nat Nat⟧ := by
  ext Q : 2
  xwp

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
    generalize h : greedySpanner G t = x
    apply Idd.by_wp h
    xwp
    xapp (Specs.forIn_list (PostCond.total fun (f_H, xs) => ∀ i j, f_H i j → 2*t-1 < _root_.dist f_H s(i,j)) ?hstep)
    case hstep =>
      intro f_H pref e suff h hinv
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

def fib_impl (n : Nat) : Idd Nat := do
  if n = 0 then return 0
  let mut a := 0
  let mut b := 1
  for _ in [1:n] do
    let a' := a
    a := b
    b := a' + b
  return b

@[reducible]
def fib_spec : Nat → Nat
| 0 => 0
| 1 => 1
| n+2 => fib_spec n + fib_spec (n+1)

theorem fib_triple : ⦃⌜True⌝⦄ fib_impl n ⦃⇓ r => ⌜r = fib_spec n⌝⦄ := by
  unfold fib_impl
  intro h
  xwp
  if h : n = 0 then simp[h] else
  simp[h]
  xapp Specs.forIn_list ?inv ?step
  case inv => exact PostCond.total fun (⟨a, b⟩, xs) => a = fib_spec xs.rpref.length ∧ b = fib_spec (xs.rpref.length + 1)
  case pre => simp_all
  case step => intros; xwp; simp_all
  intro _ _
  simp_all[Nat.sub_one_add_one]

theorem fib_correct {n} : (fib_impl n).run = fib_spec n := by
  generalize h : (fib_impl n).run = x
  apply Idd.by_wp h
  apply fib_triple True.intro

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

axiom IO.rand_spec {n : Nat} : ⦃True⦄ (IO.rand 0 n : IO Nat) ⦃⇓r => r < n⦄

/-- The result has the same parity as the input. -/
@[spec]
theorem addRandomEvens_spec (n k) : ⦃True⦄ (addRandomEvens n k) ⦃⇓r => r % 2 = k % 2⦄ := by
  unfold addRandomEvens -- TODO: integrate into xwp or xstart, make it an option
  xwp
  intro h
  xapp -- Specs.forIn_list_const_inv -- is the one that is registered
  intro hd b hinv
  xwp
  xapp IO.rand_spec
  intro h r; simp_all -- sgrind

/-- Since we're adding even numbers to our number twice, and summing,
the entire result is even. -/
theorem program_spec (n k) : ⦃True⦄ program n k ⦃⇓r => r % 2 = 0⦄ := by
  unfold program
  xwp
  intro h
  xapp (addRandomEvens_spec n k); intro r₁ h₁
  xapp /- registered spec is taken -/; intro r₂ h₂
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

section WeNeedAProofMode

private abbrev theNat : SVal [Nat, Bool] Nat := fun n b => n
private def test (P Q : PreCond (.arg Nat (.arg Bool .pure))) : PreCond (.arg Char (.arg Nat (.arg Bool .pure))) :=
  spred(fun n => ((∀ y, if y = n then ⌜‹Nat›ₛ + #theNat = 4⌝ else Q) ∧ Q) → P → (∃ x, P → if (x : Bool) then Q else P))

abbrev M := StateT Nat (StateT Char (StateT Bool (StateT String Idd)))

axiom op : Nat → M Nat

noncomputable def prog (n : Nat) : M Nat := do
  let a ← op n
  let b ← op a
  let c ← op b
  return (a + b + c)

axiom isValid : Nat → Char → Bool → String → Prop

axiom op.spec {n} : ⦃isValid⦄ op n ⦃⇓r => ⌜r > 42⌝ ∧ isValid⦄

theorem prog.spec : ⦃isValid⦄  prog n ⦃⇓r => ⌜r > 100⌝ ∧ isValid⦄ := by
  unfold prog
  intro a b c d h
  xapp op.spec
  intro r₁ a b c d ⟨hr₁, h⟩
  xapp op.spec
  intro r₂ a b c d ⟨hr₂, h⟩
  xapp op.spec
  intro r₃ a b c d ⟨hr₃, h⟩
  xpure
  simp_all only [SPred.idiom_cons, SPred.idiom_nil, SPred.and_cons, SPred.and_nil,
    and_true, gt_iff_lt]
  omega

theorem prog.spec' : ⦃isValid⦄ prog n ⦃⇓r => ⌜r > 100⌝ ∧ isValid⦄ := by
  unfold prog
  mintro □h
  mspec op.spec
  mcases h with ⟨⌜hr₁⌝, □h⟩
  mspec op.spec
  mcases h with ⟨⌜hr₂⌝, □h⟩
  mspec op.spec
  mcases h with ⟨⌜hr₃⌝, □h⟩
  mspec
  mrefine ⟨?_, h⟩
  mpure_intro
  omega

end WeNeedAProofMode
