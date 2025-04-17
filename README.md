# `mpl`

A Lean library implementing a Monadic Program Logic.
That is, a Floyd-Hoare-style program logic for functional correctness proofs of programs written using Lean's `do` notation.
It supports both automated and interactive proofs, intrinsic or extrinsic to the program syntax.
Here is an example for an automated, intrinsic proof relating an imperative implementation `fib_impl` of the Fibonacci function to its recursive specification `fib_spec`, declaring postconditions and invariants using extended `def` syntax:

```lean
abbrev fib_spec : Nat → Nat
| 0 => 0
| 1 => 1
| n+2 => fib_spec n + fib_spec (n+1)

def fib_impl (n : Nat) : Idd Nat
  ensures r => r = fib_spec n
:= do
  if n = 0 then return 0
  let mut a := 0
  let mut b := 1
  invariant xs => a = fib_spec xs.rpref.length ∧ b = fib_spec (xs.rpref.length + 1)
  for _ in [1:n] do
    let a' := a
    a := b
    b := a' + b
  return b
```

This produces an automated proof for the Hoare triple

```
fib_impl.spec (n : ℕ) : ⦃⌜True⌝⦄ fib_impl n ⦃⇓r => r = fib_spec n⦄
```

Which can be used to prove that `(fib_impl n).run = fib_spec n`:

```lean
theorem fib_correct {n} : (fib_impl n).run = fib_spec n := by
  generalize h : (fib_impl n).run = x
  apply Idd.by_wp h
  apply fib_impl.spec n True.intro
```

The proof can also be conducted extrinsically and interactively (TODO: Revisit example once the proof mode has been properly integrated and tactics have been renamed):

```lean
theorem fib_triple : ⦃⌜True⌝⦄ fib_impl n ⦃⇓ r => r = fib_spec n⦄ := by
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
```

# Key features

* **Monad-agnostic**: You can instantiate this framework at any particular monad your program is written in. Batteries are included for working with standard monad transformer stacks such as `StateT`, `ExceptT`, `ReaderT`, `Id` and `IO`. 
* **Semi-automated**: The full spectrum of automation is available: Start trying a fully automated proof, fall back to automatic generation of manually discharged verification conditions, and perform Iris-style interactive proofs in a dedicated proof mode for the leftovers.
* **Functional correctness**: The framework offers a unary program logic for functional correctness proofs. As of yet there are no plans to support relational program logics.