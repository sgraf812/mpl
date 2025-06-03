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
  mvcgen
  case inv => exact (⇓ (r, xs) => (∀ x, x ∈ xs.suff → x ≤ 5) ∧ r + xs.suff.length * 5 ≤ 25)
  all_goals simp_all +decide; try omega

def mkFreshNat [Monad m] [MonadStateOf (Nat × Nat) m] : m Nat := do
  let n ← Prod.fst <$> get
  modify (fun s => (s.1 + 1, s.2))
  pure n

private abbrev fst : SVal ((Nat × Nat)::σs) Nat := fun s => SVal.pure s.1
private abbrev snd : SVal ((Nat × Nat)::σs) Nat := fun s => SVal.pure s.2

@[spec]
theorem mkFreshNat_spec [Monad m] [WPMonad m sh] :
  ⦃⌜#fst = n ∧ #snd = o⌝⦄
  (mkFreshNat : StateT (Nat × Nat) m Nat)
  ⦃⇓ r => ⌜r = n ∧ #fst = n + 1 ∧ #snd = o⌝⦄ := by
  mintro _
  unfold mkFreshNat
  mvcgen
  simp

@[wp_simp]
theorem StateT.mkFreshNat_apply [Monad m] [LawfulMonad m] [WPMonad m sh] :
  wp⟦(mkFreshNat : StateT (Nat × Nat) m Nat)⟧ Q = fun s => Q.1 s.1 (s.1 + 1, s.2) := by
    unfold mkFreshNat; wp_simp

def mkFreshPair : StateM (Nat × Nat) (Nat × Nat) := do
  let a ← mkFreshNat
  let b ← mkFreshNat
  pure (a, b)

theorem mkFreshPair_spec :
  ⦃⌜True⌝⦄
  mkFreshPair
  ⦃⇓ (a, b) => ⌜a ≠ b⌝⦄ := by
  unfold mkFreshPair
  mintro -
  mspec mkFreshNat_spec
  mintro ∀s
  mcases h with ⌜h₁⌝
  mspec mkFreshNat_spec
  mintro ∀s
  mcases h with ⌜h₂⌝
  simp_all [h₁, h₂]

theorem mkFreshPair_spec_no_eta :
  ⦃⌜True⌝⦄
  mkFreshPair
  ⦃⇓ (a, b) => ⌜a ≠ b⌝⦄ := by
  unfold mkFreshPair
  mintro -
  mspec mkFreshNat_spec
  mspec mkFreshNat_spec
  mspec
  intro _; simp_all

example : PostCond (Nat × List.Zipper (List.range' 1 3 1)) (PostShape.except Nat (PostShape.arg Nat PostShape.pure)) :=
  ⟨fun (r, xs) s => r ≤ 4 ∧ s = 4 ∧ r + xs.suff.sum > 4, fun e s => e = 42 ∧ s = 4, ()⟩

example : PostCond (Nat × List.Zipper (List.range' 1 3 1)) (PostShape.except Nat (PostShape.arg Nat PostShape.pure)) :=
  post⟨fun (r, xs) s => r ≤ 4 ∧ s = 4 ∧ r + xs.suff.sum > 4, fun e s => e = 42 ∧ s = 4⟩

example : (Nat × List.Zipper (List.range' 1 3 1)) → Assertion (PostShape.except Nat (PostShape.arg Nat PostShape.pure)) :=
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
  mvcgen
  case inv => exact (⇓ (p, xs) s => True)
  all_goals simp
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
  mvcgen
  case inv => exact post⟨fun (r, xs) s => r ≤ 4 ∧ s = 4 ∧ r + xs.suff.sum > 4, fun e s => e = 42 ∧ s = 4⟩
  case post.success => simp at h; omega
  case post.except => simp
  case ifTrue => intro _; simp_all
  case ifFalse => intro _; simp; omega
  simp_all +decide

example :
  (wp (m:= ExceptT Nat (StateT Nat (ReaderT Bool Id))) (withTheReader Bool not (do if (← read) then return 0 else return 1))).apply Q
  ⊣⊢ₛ
  (wp (m:= ExceptT Nat (StateT Nat (ReaderT Bool Id))) (do if (← read) then return 1 else return 0)).apply Q := by
    apply SPred.bientails.iff.mpr
    constructor
    all_goals mstart; mwp; simp [SVal.ite_app] -- TODO: Do we need mvcgen at h? Alas, mvcgen does not generate bientailments.

example :
  (wp (m:= ReaderT Char (StateT Bool (ExceptT Nat Id))) (do set true; throw 42; set false; get)).apply Q
  ⊣⊢ₛ
  (wp (m:= ReaderT Char (StateT Bool (ExceptT Nat Id))) (do set true; throw 42; get)).apply Q := by
    apply SPred.bientails.iff.mpr
    constructor
    all_goals mstart; mwp

example :
  (wp (m:= ReaderT Char (StateT Bool (ExceptT Nat Id)))
      (do try { set true; throw 42 } catch _ => set false; get)).apply Q
  ⊣⊢ₛ
  (wp (m:= ReaderT Char (StateT Bool (ExceptT Nat Id)))
      (do set false; get)).apply Q := by
    apply SPred.bientails.iff.mpr
    constructor <;> mwp

theorem test_loop_break :
  ⦃⌜‹Nat›ₛ = 42⌝⦄
  do
    let mut x := 0
    let s ← get
    for i in [1:s] do { x := x + i; if x > 4 then break }
    (set 1 : StateT Nat Idd PUnit)
    return x
  ⦃⇓ r => ⌜r > 4 ∧ ‹Nat›ₛ = 1⌝⦄ := by
  mvcgen
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
  do
    let mut x := 0
    let s ← get
    for i in [1:s] do { x := x + i; if x > 4 then return 42 }
    (set 1 : StateT Nat Idd PUnit)
    return x
  ⦃⇓ r s => r = 42 ∧ s = 4⦄ := by
  mvcgen
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

example : wp⟦do try { throw 42; return 1 } catch _ => return 2 : Except Nat Nat⟧ Q
          ⊣⊢ₛ
          wp⟦pure 2 : Except Nat Nat⟧ Q := by
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

abbrev fib_spec : Nat → Nat
| 0 => 0
| 1 => 1
| n+2 => fib_spec n + fib_spec (n+1)

--theorem fib_triple : ⦃⌜True⌝⦄ fib_impl n ⦃⇓ r => r = fib_spec n⦄ := by
--  unfold fib_impl
--  dsimp
--  mintro _
--  if h : n = 0 then simp [h] else
--  simp only [h, reduceIte]
--  mspec
--  mspec_no_bind Specs.bind
--  set_option trace.mpl.tactics.spec true in
--  mspec_no_bind Specs.forIn_list (⇓ (⟨a, b⟩, xs) => a = fib_spec xs.rpref.length ∧ b = fib_spec (xs.rpref.length + 1)) ?step
--
--  case step => dsimp; intros; mintro _; simp_all
--  simp_all [Nat.sub_one_add_one]

theorem fib_triple : ⦃⌜True⌝⦄ fib_impl n ⦃⇓ r => r = fib_spec n⦄ := by
  unfold fib_impl
  dsimp
  mintro _
  if h : n = 0 then simp [h] else
  simp only [h, reduceIte]
  mspec -- Specs.pure
  mspec Specs.forIn_range (⇓ (⟨a, b⟩, xs) => a = fib_spec xs.rpref.length ∧ b = fib_spec (xs.rpref.length + 1)) ?step
  case step => dsimp; intros; mintro _; simp_all
  simp_all [Nat.sub_one_add_one]

#check fib_impl.fun_cases
theorem fib_triple_cases : ⦃⌜True⌝⦄ fib_impl n ⦃⇓ r => r = fib_spec n⦄ := by
  apply fib_impl.fun_cases n _ ?case1 ?case2
  case case1 => rintro rfl; mintro -; simp only [fib_impl, ↓reduceIte]; mspec
  case case2 =>
  intro h
  mintro -
  simp only [fib_impl, h, reduceIte]
  mspec
  mspec Specs.forIn_range (⇓ (⟨a, b⟩, xs) => a = fib_spec xs.rpref.length ∧ b = fib_spec (xs.rpref.length + 1)) ?step
  case step => dsimp; intros; mintro _; mwp; simp_all
  simp_all [Nat.sub_one_add_one]

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
  apply fib_impl.fun_cases n _ ?case1 ?case2
  case case1 => intro h; simp only [fib_impl, h, ↓reduceIte]; mstart; mspec
  case case2 =>
  intro hn
  simp only [fib_impl, hn, ↓reduceIte]
  mstart
  mspec
  mspec
  case pre1 => mpure_intro; exact loop_pre n hn
  case post.success => mspec; mpure_intro; apply_rules [loop_post]
  case step =>
    intro _ _ _ _ h;
    mintro _;
    mspec
    mspec
    mpure_intro
    apply_rules [loop_step]

theorem fib_triple_vcs : ⦃⌜True⌝⦄ fib_impl n ⦃⇓ r => r = fib_spec n⦄ := by
  intro _
  apply fib_impl_vcs
  case I => intro n hn; exact (⇓ (⟨a, b⟩, xs) => a = fib_spec xs.rpref.length ∧ b = fib_spec (xs.rpref.length + 1))
  case ret => rfl
  case loop_pre => intros; trivial
  case loop_post => simp_all[Nat.sub_one_add_one]
  case loop_step => simp_all

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
  mspec Specs.forIn_list_const_inv
  mspec
  intro n r
  mintro ⌜h⌝
  mspec IO.rand_spec
  simp_all -- sgrind

/-- Since we're adding even numbers to our number twice, and summing,
the entire result is even. -/
theorem program_spec (n k) : ⦃True⦄ program n k ⦃⇓r => r % 2 = 0⦄ := by
  unfold program
  mintro -
  mspec (addRandomEvens_spec n k)
  mpure h
  mspec /- registered spec is taken -/
  mpure h
  mspec
  mpure_intro
  omega  -- grind -- can't do it; check after 4.17 release

end KimsBabySteps

section WeNeedAProofMode

private abbrev theNat : SVal [Nat, Bool] Nat := fun n _ => n
private def test (P Q : Assertion (.arg Nat (.arg Bool .pure))) : Assertion (.arg Char (.arg Nat (.arg Bool .pure))) :=
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
  mintro h
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
