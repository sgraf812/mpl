/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
import MPL.Idd

namespace MPL.Test.Code

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

def ifs (n : Nat) : Idd Nat := do
  let mut x := 0
  if n > 0 then x := x + 1 else x := x + 2
  if n > 1 then x := x + 1 else x := x + 2
  return x

abbrev AppState := Nat × Nat

def mkFreshNat [Monad m] [MonadStateOf AppState m] : m Nat := do
  let n ← Prod.fst <$> get
  modify (fun s => (s.1 + 1, s.2))
  pure n

def mkFreshPair : StateM AppState (Nat × Nat) := do
  let a ← mkFreshNat
  let b ← mkFreshNat
  pure (a, b)

def sum_loop : Idd Nat := do
  let mut x := 0
  for i in [1:5] do x := x + i
  return x

def throwing_loop : ExceptT Nat (StateT Nat Idd) Nat := do
  let mut x := 0
  let s ← get
  for i in [1:s] do { x := x + i; if x > 4 then throw 42 }
  (set 1 : ExceptT Nat (StateT Nat Idd) PUnit)
  return x

def breaking_loop : StateT Nat Idd Nat := do
  let mut x := 0
  let s ← get
  for i in [1:s] do { x := x + i; if x > 4 then break }
  set 1
  return x

def returning_loop : StateT Nat Idd Nat := do
  let mut x := 0
  let s ← get
  for i in [1:s] do { x := x + i; if x > 4 then return 42 }
  set 1
  return x

def unfold_to_expose_match : StateM Nat Nat :=
  (some get).getD (pure 3)
