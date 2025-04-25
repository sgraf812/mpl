/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
import Lean
import MPL
import MPL.IO

namespace MPL.Test.Toy
open MPL

set_option grind.warning false

theorem test_sum :
  ⦃True⦄
  do
    let mut x := 0
    for i in [1:5] do
      x := x + i
    pure (f := Idd) x
  ⦃⇓r => r < 30⦄ := by
  mintro -
  mwp
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
  mwp
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
  mwp
  simp

example : PostCond (Nat × List.Zipper (List.range' 1 3 1)) (PostShape.except Nat (PostShape.arg Nat PostShape.pure)) :=
  ⟨fun (r, xs) s => r ≤ 4 ∧ s = 4 ∧ r + xs.suff.sum > 4, fun e s => e = 42 ∧ s = 4, ()⟩

example : PostCond (Nat × List.Zipper (List.range' 1 3 1)) (PostShape.except Nat (PostShape.arg Nat PostShape.pure)) :=
  post⟨fun (r, xs) s => r ≤ 4 ∧ s = 4 ∧ r + xs.suff.sum > 4, fun e s => e = 42 ∧ s = 4⟩

example : (Nat × List.Zipper (List.range' 1 3 1)) → PreCond (PostShape.except Nat (PostShape.arg Nat PostShape.pure)) :=
  let x := ⟨fun (r, xs) s => r ≤ 4 ∧ s = 4 ∧ r + xs.suff.sum > 4, fun e s => e = 42 ∧ s = 4⟩; Prod.fst x

example :
  ⦃fun s => s = 4⦄
  do
    let mut x := 0
    for i in [1:4] do { x := x + i }
    (pure () : (StateT Nat Idd) Unit)
    return x
  ⦃⇓ _ _ => True⦄ := by
  mintro hs
  mwp
  mspec (Specs.forIn_list (⇓ (p, xs) s => True) ?step)
  case step => intros; mintro h; simp
  mintro ∀s
  simp

theorem test_ex :
  ⦃fun s => s = 4⦄
  do
    let mut x := 0
    let s ← get
    for i in [1:s] do { x := x + i; if x > 4 then throw 42 }
    (set 1 : ExceptT Nat (StateT Nat Idd) PUnit)
    return x
  ⦃post⟨fun _ _ => False,
        fun e s => e = 42 ∧ s = 4⟩⦄ := by
  mintro hs ∀s
  mpure hs
  subst hs
  mwp
--  set_option trace.mpl.tactics.spec true in
  mspec (Specs.forIn_list post⟨fun (r, xs) s => r ≤ 4 ∧ s = 4 ∧ r + xs.suff.sum > 4, fun e s => e = 42 ∧ s = 4⟩ ?step)
  case step =>
    intro b pref x suff h
    mintro H
    mwp
    simp only [h, List.sum_cons]
    mintro ∀b'
    mpure H
    mpure_intro
    split
    · grind
    · simp only [PredTrans.pure_apply]; omega
  simp only [List.sum_nil]
  mintro ∀s
  mpure h
  omega -- sgrind

example :
  (wp (m:= ExceptT Nat (StateT Nat (ReaderT Bool Id))) (withTheReader Bool not (do if (← read) then return 0 else return 1))).apply Q
  ⊣⊢ₛ
  (wp (m:= ExceptT Nat (StateT Nat (ReaderT Bool Id))) (do if (← read) then return 1 else return 0)).apply Q := by
    apply SPred.bientails.iff.mpr
    constructor
    all_goals mstart; mwp; simp [SVal.ite_app]

example :
  (wp (m:= ReaderT Char (StateT Bool (ExceptT Nat Id))) (do set true; throw 42; set false; get)).apply Q
  ⊣⊢ₛ
  (wp (m:= ReaderT Char (StateT Bool (ExceptT Nat Id))) (do set true; throw 42; get)).apply Q := by
    apply SPred.bientails.iff.mpr
    constructor
    all_goals mstart; mwp

example :
  (wp (m:= ReaderT Char (StateT Bool (ExceptT Nat Id))) (do try { set true; throw 42 } catch _ => set false; get)).apply Q
  ⊣⊢ₛ
  (wp (m:= ReaderT Char (StateT Bool (ExceptT Nat Id))) (do set false; get)).apply Q := by
    apply SPred.bientails.iff.mpr
    constructor
    all_goals mstart; mwp

theorem test_loop_break :
  ⦃⌜‹Nat›ₛ = 42⌝⦄
  do
    let mut x := 0
    let s ← get
    for i in [1:s] do { x := x + i; if x > 4 then break }
    (set 1 : StateT Nat Idd PUnit)
    return x
  ⦃⇓ r => ⌜r > 4 ∧ ‹Nat›ₛ = 1⌝⦄ := by
  mintro hs ∀s
  mpure hs
  mwp
  mspec (Specs.forIn_list (⇓ (r, xs) s => (r ≤ 4 ∧ r = xs.rpref.sum ∨ r > 4) ∧ s = 42) ?step)
  case step =>
    intro b pref x suff h
    mintro H ∀b'
    mpure H
    split
    · simp_all
    · simp_all; omega
  case post.success =>
    mintro ∀s
    subst_vars
    dsimp
    (conv in (List.sum _) => whnf)
    simp_all
    omega
  simp_all

theorem get_spec [Monad m] [WPMonad m ps] {Q : PostCond σ (.arg σ ps)} :
  ⦃fun s => Q.1 s s⦄ (get : StateT σ m σ) ⦃Q⦄ := by mintro h; mwp

theorem test_loop_early_return :
  ⦃fun s => s = 4⦄
  do
    let mut x := 0
    let s ← get
    for i in [1:s] do { x := x + i; if x > 4 then return 42 }
    (set 1 : StateT Nat Idd PUnit)
    return x
  ⦃⇓ r s => r = 42 ∧ s = 4⦄ := by
  mintro hs ∀s
  mpure hs
  subst hs
  simp only [gt_iff_lt, bind_pure_comp, map_pure, Std.Range.forIn_eq_forIn_range', Std.Range.size,
    Nat.div_one, pure_bind]
  mspec get_spec
  mspec (Specs.forIn_list (⇓ (r, xs) s => (r.1 = none ∧ r.2 = xs.rpref.sum ∧ r.2 ≤ 4 ∨ r.1 = some 42 ∧ r.2 > 4) ∧ s = 4) ?step)
  case pre => simp
  case step =>
    intro b pref x suff h
    mintro ⟨h, hs⟩
    mintro ∀s
    mpure hs
    subst hs
    mwp
    simp_all only [Nat.add_one_sub_one, PostShape.args, SPred.and_nil, gt_iff_lt, SPred.or_nil,
      List.reverse_append, List.reverse_cons, List.reverse_reverse, List.append_assoc,
      List.singleton_append, List.sum_cons, false_and, and_self, or_true, true_and,
      or_false, SVal.ite_app, and_true, if_true_left, SPred.entails_nil]
    omega
  rcases r with ⟨r, x⟩
  mintro ∀s'
  mcases h with ⟨h,hs'⟩
  subst hs'
  cases r
  case none => simp at h; (conv at h in (List.sum _) => whnf); exfalso; have ⟨h₁,h₂⟩ := h; subst_vars; contradiction -- omega -- WTF why doesn't omega
  case some r => simp_all

example : wp⟦do try { throw 42; return 1 } catch _ => return 2 : Except Nat Nat⟧.apply Q
          ⊣⊢ₛ
          wp⟦pure 2 : Except Nat Nat⟧.apply Q := by
  apply SPred.bientails.iff.mpr
  constructor
  all_goals mstart; mwp

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
  mintro _
  if h : n = 0 then simp [h] else
  simp only [h]
  mwp
  mspec Specs.forIn_list ?inv ?step
  case inv => exact PostCond.total fun (⟨a, b⟩, xs) => a = fib_spec xs.rpref.length ∧ b = fib_spec (xs.rpref.length + 1)
  case pre => simp_all
  case step => intros; mintro _; mwp; simp_all
  simp_all [Nat.sub_one_add_one]

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

open scoped MPL.IO

/-- The result has the same parity as the input. -/
@[spec]
theorem addRandomEvens_spec (n k) : ⦃True⦄ (addRandomEvens n k) ⦃⇓r => r % 2 = k % 2⦄ := by
  unfold addRandomEvens
  mintro -
  mwp
  let _ := inferInstanceAs (WPMonad IO _)
  mspec Specs.forIn_list_const_inv -- is the one that is registered
  · exact inferInstance
  intro n r
  mintro ⌜h⌝
  mwp
  mspec IO.rand_spec
  simp_all -- sgrind

/-- Since we're adding even numbers to our number twice, and summing,
the entire result is even. -/
theorem program_spec (n k) : ⦃True⦄ program n k ⦃⇓r => r % 2 = 0⦄ := by
  unfold program
  mintro -
  mwp
  mspec (addRandomEvens_spec n k)
  mpure h
  mspec /- registered spec is taken -/
  mpure h
  mpure_intro
  omega  -- grind -- can't do it; check after 4.17 release

end KimsBabySteps

section WeNeedAProofMode

private abbrev theNat : SVal [Nat, Bool] Nat := fun n _ => n
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
