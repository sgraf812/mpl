/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
import MPL.ProofMode.Tactics.Basic
import MPL.WPSimp
import MPL.WP
import MPL.WPMonad
import MPL.WPMonadLift
import MPL.WPMonadFunctor
import MPL.WPMonadExceptOf

import MPL.ProofMode.Tactics.Intro
import MPL.ProofMode.Tactics.WP
import MPL.ProofMode.Tactics.Spec
import MPL.Triple

/-!
# Tactic `mvcgen`
-/

namespace MPL.ProofMode.Tactics
open Lean Elab Tactic Meta



elab "mvcgen" : tactic => do
  let (mvar, goal) ← mStart (← getMainGoal)
  replaceMainGoal mvars

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

theorem fib_triple : ⦃⌜True⌝⦄ fib_impl n ⦃⇓ r => r = fib_spec n⦄ := by
  unfold fib_impl
  dsimp
  mintro _
  if h : n = 0 then simp [h] else
  simp only [h]
  mwp
  mspec Specs.forIn_list (⇓ (⟨a, b⟩, xs) => a = fib_spec xs.rpref.length ∧ b = fib_spec (xs.rpref.length + 1)) ?step
  case step => dsimp; intros; mintro _; mwp; simp_all
  simp_all [Nat.sub_one_add_one]

theorem fib_triple_vc : ⦃⌜True⌝⦄ fib_impl n ⦃⇓ r => r = fib_spec n⦄ := by
  unfold fib_impl
  mstart
  mvcgen
--  dsimp
--  mintro _
--  if h : n = 0 then simp [h] else
--  simp only [h]
--  mwp
--  mspec Specs.forIn_list (⇓ (⟨a, b⟩, xs) => a = fib_spec xs.rpref.length ∧ b = fib_spec (xs.rpref.length + 1)) ?step
--  case step => dsimp; intros; mintro _; mwp; simp_all
--  simp_all [Nat.sub_one_add_one]
