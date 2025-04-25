/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
-- This type exists purely because of the following annoying simp rules:
--#check Id.map_eq
--#check Id.bind_eq
--#check Id.pure_eq

@[irreducible]
def Idd (α : Type u) := α

def Idd.run (x : Idd α) : α := cast (by unfold Idd; rfl) x

@[ext]
def Idd.ext {α : Type u} {a b : Idd α} (h : a.run = b.run) : a = b := by with_unfolding_all (exact h)

def Idd.pure (a : α) : Idd α := cast (by unfold Idd; rfl) a

def Idd.bind (x : Idd α) (f : α → Idd β) : Idd β := f x.run
instance : Monad Idd where
  pure := Idd.pure
  bind := Idd.bind

@[simp]
theorem Idd.run_pure (a : α) : Idd.run (Pure.pure a) = a := by with_unfolding_all rfl

@[simp]
theorem Idd.bind_pure (x : Idd α) (f : α → Idd β) : (x >>= f).run = (f x.run).run := by with_unfolding_all rfl

@[simp]
theorem Idd.map_pure (x : Idd α) (f : α → β) : (f <$> x).run = f x.run := by with_unfolding_all rfl

instance Idd.instLawfulMonad : LawfulMonad Idd :=
  LawfulMonad.mk'
    (id_map := by intro _ x; ext; simp)
    (pure_bind := by intro _ _ x f; ext; simp)
    (bind_assoc := by intro _ _ _ x f g; ext; simp)
