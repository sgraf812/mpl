import MPL
import MPL.Do

open MPL

-- Hoare triple specifications defined in terms of weakest precondition predicate transformers

def AppState := Nat × Nat

def mkFreshInt [Monad m] [MonadStateOf AppState m] : m Nat := do
  let n ← Prod.fst <$> get
  modify (fun s => (s.1 + 1, s.2))
  pure n

private abbrev st : SVal (AppState::σs) (Nat × Nat) := fun s => SVal.pure s

@[spec]
theorem mkFreshInt_spec [Monad m] [WPMonad m sh] :
  ⦃⌜(#st).1 = n ∧ (#st).2 = o⌝⦄
  (mkFreshInt : StateT AppState m Nat)
  ⦃⇓ r => ⌜r = n ∧ (#st).1 = n + 1 ∧ (#st).2 = o⌝⦄ := by
  unfold mkFreshInt
  xstart
  intro s
  xwp
  simp

#print triple
#print WP.wp
#print PredTrans















-- wp_simp rules:

#check WP.bind_apply
#check StateT.get_apply
#check MonadStateOf.modify_apply













-- intrinsic verification

def mkFreshInt' {m : Type → Type} [Monad m] : StateT AppState m Nat
  forall {ps} [WPMonad m ps] (n o : Nat)
  requires s => PreCond.pure (s.1 = n ∧ s.2 = o)
  ensures r s => PreCond.pure (r = n ∧ s.1 = n + 1 ∧ s.2 = o)
:= do
  let n ← Prod.fst <$> get
  modify (fun s => (s.1 + 1, s.2))
  pure n

#print mkFreshInt'.spec





















-- compositional proofs using Hoare triple specifications

def mkFreshPair : StateM AppState (Nat × Nat) := do
  let a ← mkFreshInt
  let b ← mkFreshInt
  pure (a, b)

@[spec]
theorem mkFreshPair_spec :
  ⦃PreCond.pure True⦄
  mkFreshPair
  ⦃⇓ (a, b) => ⌜a ≠ b⌝⦄ := by
  unfold mkFreshPair
  xstart
  xwp
  intro s hs
  xapp mkFreshInt_spec
  intro a s₁ hs₁
  xapp mkFreshInt_spec
  intro b s₂ hs₂
  simp_all[hs₁, hs₂]

-- eliminating a Hoare triple spec into the pure world

theorem mkFreshPair_correct : ∀ s, let (a,b) := (mkFreshPair s).1; a ≠ b :=
  fun s => mkFreshPair_spec s True.intro
















-- loop invariants

#print Idd
#print Specs.forIn_list
#print List.Zipper

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

theorem fib_triple : ⦃True⦄ fib_impl n ⦃⇓ r => r = fib_spec n⦄ := by
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

-- intrisically:

def fib_impl' (n : Nat) : Idd Nat
  ensures r => r = fib_spec n
:= do
  if n = 0 then return 0
  let mut a := 0
  let mut b := 1
  assert => a = 0 ∧ b = 1
  invariant xs => a = fib_spec xs.rpref.length ∧ b = fib_spec (xs.rpref.length + 1)
  for _ in [1:n] do
    let a' := a
    a := b
    b := a' + b
  return b

#check fib_impl'.spec


















-- exceptions, transformer stacks

example :
  ⦃fun s => s = 4⦄
  (do
    let mut x := 0
    let s ← get
    for i in [1:s] do -- i in [1,2,3,4], x = [0,1,3,6,10]
      x := x + i
      if x > 4 then throw 42
    set 1
    return x
    : ExceptT Nat (StateT Nat Idd) PUnit)
  ⦃(fun r s => False,
    fun e s => e = 42 ∧ s = 4,
    ())⦄ := by
  xstart
  intro s hs
  xwp
  xapp (Specs.forIn_list (fun (r, xs) s => r ≤ 4 ∧ s = 4 ∧ r + xs.suff.sum > 4, fun e s => e = 42 ∧ s = 4, ()) ?step)
  case pre => subst hs; decide
  case step =>
    intro b pref x suff h
    xstart
    xwp
    simp only [h, List.sum_cons]
    intro b' hinv
    split
    · grind
    · simp only [PredTrans.pure_apply]; omega
  simp only [List.sum_nil, add_zero]
  intro _ _; simp; omega -- grind in 4.17
