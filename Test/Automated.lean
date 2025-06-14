import MPL
import Test.Code

/-!
This module tests `mvcgen` by maximally automating many of the proofs in `ByHand.lean`.
-/

namespace MPL.Test.VC

open MPL.Test.Code

theorem fib_triple : ⦃⌜True⌝⦄ fib_impl n ⦃⇓ r => r = fib_spec n⦄ := by
  unfold fib_impl
  mvcgen
  case inv => exact ⇓ (⟨a, b⟩, xs) =>
    a = fib_spec xs.rpref.length ∧ b = fib_spec (xs.rpref.length + 1)
  all_goals simp_all +zetaDelta [Nat.sub_one_add_one]

theorem fib_triple_step : ⦃⌜True⌝⦄ fib_impl n ⦃⇓ r => r = fib_spec n⦄ := by
  unfold fib_impl
  mvcgen_step 14 -- 13 still has a wp⟦·⟧
  case inv => exact ⇓ (⟨a, b⟩, xs) =>
    a = fib_spec xs.rpref.length ∧ b = fib_spec (xs.rpref.length + 1)
  all_goals simp_all +zetaDelta [Nat.sub_one_add_one]

attribute [local spec] fib_triple in
theorem fib_triple_attr : ⦃⌜True⌝⦄ fib_impl n ⦃⇓ r => r = fib_spec n⦄ := by
  mvcgen

attribute [local spec] fib_triple in
theorem fib_triple_erase : ⦃⌜True⌝⦄ fib_impl n ⦃⇓ r => r = fib_spec n⦄ := by
  mvcgen [-fib_triple] -- should not make any progress
  fail_if_success done
  admit

theorem fib_impl_vcs
    (Q : Nat → PostCond Nat PostShape.pure)
    (I : (n : Nat) → (_ : ¬n = 0) →
      PostCond (MProd Nat Nat × List.Zipper [1:n].toList) PostShape.pure)
    (ret : (Q 0).1 0)
    (loop_pre : ∀ n (hn : ¬n = 0), (I n hn).1 (⟨0, 1⟩, List.Zipper.begin _))
    (loop_post : ∀ n (hn : ¬n = 0) r, (I n hn).1 (r, List.Zipper.end _) ⊢ₛ (Q n).1 r.snd)
    (loop_step : ∀ n (hn : ¬n = 0) r rpref x suff (h : [1:n].toList = rpref.reverse ++ x :: suff),
                  (I n hn).1 (r, ⟨rpref, x::suff, by simp[h]⟩) ⊢ₛ (I n hn).1 (⟨r.2, r.1+r.2⟩, ⟨x::rpref, suff, by simp[h]⟩))
    : wp⟦fib_impl n⟧ (Q n) := by
  unfold fib_impl
  mvcgen
  case inv h => exact I n h
  case ifTrue h => subst h; mpure_intro; exact ret
  case ifFalse h => mpure_intro; apply_rules [loop_pre]
  case step => mpure_intro; apply_rules [loop_step]
  case post.success => mpure_intro; apply_rules [loop_post]

-- TODO: Use strongest post
theorem ifs_triple : ⦃⌜True⌝⦄ ifs n ⦃⇓ r => ⌜r > 0⌝⦄ := by
  unfold ifs
  mvcgen_no_trivial <;> try (mpure_intro; trivial) -- this is the default for mvcgen

private abbrev fst : SVal (AppState::σs) Nat := fun s => SVal.pure s.1
private abbrev snd : SVal (AppState::σs) Nat := fun s => SVal.pure s.2

@[spec]
theorem mkFreshNat_spec [Monad m] [WPMonad m sh] :
  ⦃⌜#fst = n ∧ #snd = o⌝⦄
  (mkFreshNat : StateT AppState m Nat)
  ⦃⇓ r => ⌜r = n ∧ #fst = n + 1 ∧ #snd = o⌝⦄ := by
  mvcgen [mkFreshNat]
  simp_all

theorem erase_unfold [Monad m] [WPMonad m sh] :
  ⦃⌜#fst = n ∧ #snd = o⌝⦄
  (mkFreshNat : StateT AppState m Nat)
  ⦃⇓ r => ⌜r = n ∧ #fst = n + 1 ∧ #snd = o⌝⦄ := by
  unfold mkFreshNat
  mvcgen [-modify]
  simp_all
  fail_if_success done
  admit

theorem add_unfold [Monad m] [WPMonad m sh] :
  ⦃⌜#fst = n ∧ #snd = o⌝⦄
  (mkFreshNat : StateT AppState m Nat)
  ⦃⇓ r => ⌜r = n ∧ #fst = n + 1 ∧ #snd = o⌝⦄ := by
  mvcgen [mkFreshNat]

theorem mkFreshPair_triple : ⦃⌜True⌝⦄ mkFreshPair ⦃⇓ (a, b) => ⌜a ≠ b⌝⦄ := by
  unfold mkFreshPair
  mvcgen
  simp_all [SPred.entails_elim_cons]

theorem sum_loop_spec :
  ⦃True⦄
  sum_loop
  ⦃⇓r => r < 30⦄ := by
  -- cf. `Toy.sum_loop_spec`
  mintro -
  mvcgen [sum_loop]
  case inv => exact (⇓ (r, xs) => (∀ x, x ∈ xs.suff → x ≤ 5) ∧ r + xs.suff.length * 5 ≤ 25)
  all_goals simp_all +decide; try omega

theorem throwing_loop_spec :
  ⦃fun s => s = 4⦄
  throwing_loop
  ⦃post⟨fun _ _ => False,
        fun e s => e = 42 ∧ s = 4⟩⦄ := by
  mvcgen [throwing_loop]
  case inv => exact post⟨fun (r, xs) s => r ≤ 4 ∧ s = 4 ∧ r + xs.suff.sum > 4,
                         fun e s => e = 42 ∧ s = 4⟩
  · simp_all only [SVal.curry_nil, SPred.entails_nil]; decide
  · simp_all only [List.sum_nil]; omega
  · simp_all
  · intro _; simp_all
  · intro _; simp_all only [List.sum_cons, true_and, SPred.entails_nil]; omega

theorem test_loop_break :
  ⦃⌜‹Nat›ₛ = 42⌝⦄
  breaking_loop
  ⦃⇓ r => ⌜r > 4 ∧ ‹Nat›ₛ = 1⌝⦄ := by
  mvcgen [breaking_loop]
  case inv => exact (⇓ (r, xs) s => (r ≤ 4 ∧ r = xs.rpref.sum ∨ r > 4) ∧ s = 42)
  case ifTrue => intro _; simp_all
  case ifFalse => intro _; simp_all; omega
  case post.success =>
    simp_all
    conv at h in (List.sum _) => whnf
    simp at h
    omega
  simp_all

theorem test_loop_early_return :
  ⦃fun s => s = 4⦄
  returning_loop
  ⦃⇓ r s => r = 42 ∧ s = 4⦄ := by
  mvcgen [returning_loop]
  case inv => exact (⇓ (r, xs) s => (r.1 = none ∧ r.2 = xs.rpref.sum ∧ r.2 ≤ 4 ∨ r.1 = some 42 ∧ r.2 > 4) ∧ s = 4)
  case ifTrue => intro _; simp_all
  case ifFalse => intro _; simp_all; omega
  case pre1 => simp_all
  case h_1 =>
    simp_all
    conv at h in (List.sum _) => whnf
    simp at h
    omega
  case h_2 => simp_all

-- theorem returning_loop_spec :
--   ⦃fun s => s = 4⦄
--   returning_loop
--   ⦃⇓ r s => r = 42 ∧ s = 4⦄ := by
--   mvcgen [returning_loop]

theorem unfold_to_expose_match_spec :
  ⦃fun s => ⌜s = 4⌝⦄
  unfold_to_expose_match
  ⦃⇓ r => ⌜r = 4⌝⦄ := by
  -- should unfold `Option.getD`, reduce the `match (some get) with | some e => e`
  -- and then apply the spec for `get`.
  set_option pp.rawOnError true in
  mvcgen [unfold_to_expose_match, Option.getD]
  -- TODO: This is weird, we should not need .rfl below.
  -- `mspec` should be able to solve this,
  -- but isDefEq seems to fail for `⌜s = 4⌝ = ⌜s = 4⌝ s`, whereas
  -- it succeeds below. It must be some Config setting, but I don't know which.
  exact .rfl

theorem test_match_splitting {m : Option Nat} (h : m = some 4) :
  ⦃⌜True⌝⦄
  (match m with
  | some n => (set n : StateM Nat PUnit)
  | none => set 0)
  ⦃⇓ r s => ⌜s = 4⌝⦄ := by
  mvcgen
  simp_all

theorem test_sum :
  ⦃True⦄
  do
    let mut x := 0
    for i in [1:5] do
      x := x + i
    pure (f := Idd) x
  ⦃⇓r => r < 30⦄ := by
  mvcgen
  case inv => exact (⇓ (r, xs) => (∀ x, x ∈ xs.suff → x ≤ 5) ∧ r + xs.suff.length * 5 ≤ 25)
  case step =>
    simp_all
    omega
  case post.success => simp_all; omega
  simp_all +decide

/--
  The main point about this test is that `mSpec` should return all unassigned MVars it creates.
  This used to be untrue because `mkForallFVars` etc. would instantiate MVars and introduce new
  unassigned MVars in turn. It is important for `mSpec` to return these new MVars, otherwise
  we get `(kernel) declaration has metavariables 'MPL.Test.VC.mspec_forwards_mvars'`
-/
theorem mspec_forwards_mvars {n : Nat} :
  ⦃⌜True⌝⦄
  (do
    for i in [2:n] do
      if n < i * i then
        return 1
    return 1 : Idd Nat)
  ⦃⇓ r => ⌜True⌝⦄ := by
  mvcgen
  all_goals admit

def check_all (p : Nat → Prop) [DecidablePred p] (n : Nat) : Bool := Id.run do
  for i in [0:n] do
    if ¬ p i then
      return false
  return true

@[simp]
theorem Std.Range.mem_toList {x} {r : Std.Range} :
    x ∈ r.toList ↔ x ∈ r := sorry

@[simp]
theorem Nat.mod_one {n : Nat} : n % 1 = 0 := by omega

/--
VC generation is normally not useful to massage hypotheses such as `ht`, but in this example
we manage to prove a contradiction `hf` using the VC generator.
-/
example (p : Nat → Prop) [DecidablePred p] (n : Nat) :
    (∀ i, i < n → p i) ↔ check_all p n := by
  constructor
  · intro h
    apply Id.by_wp (P := (· = true)) rfl
    mvcgen
    case inv => exact (⇓ (r, xs) => r.1 = none ∧ ∀ x, x ∈ xs.suff → p x)
    case pre1 => simp; intro a ha; apply h a ha.upper
    all_goals simp_all
  · intro ht i hin
    apply Classical.byContradiction
    intro h'
    have hf : check_all p n = false := by
      have hin : i ∈ [0:n] := by simp [Std.instMembershipNatRange, hin]
      apply Id.by_wp (P := (· = false)) rfl
      mvcgen
      case inv => exact (⇓ (r, xs) =>
        match r.1 with
        | none => i ∈ xs.suff
        | some b => b = false ∧ xs.suff = [])
      all_goals simp_all; try grind
    simp [ht] at hf
