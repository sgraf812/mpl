/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
import MPL.WPMonad

open MPL

structure Universe where
  U : Type
  El : U → Type

def Elts (u : Universe) : Type := Σ x, u.El x

abbrev Addr := Fin
def Heap (u : Universe) n := Addr n → Elts u

axiom IO.wp {α ε} (x : EIO ε α) : PredTrans (.except ε .pure) α
axiom IO.wp_pure {α ε} (a : α) :
  IO.wp (pure (f := EIO ε) a) = PredTrans.pure a
axiom IO.wp_bind {α β ε} (x : EIO ε α) (f : α → EIO ε β) :
  IO.wp (x >>= f) = IO.wp x >>= fun a => IO.wp (f a)

noncomputable instance IO.instWP : WP (EIO ε) (.except ε .pure) where
  wp := IO.wp

axiom IO.instLawfulMonad {ε} : LawfulMonad (EIO ε)
scoped instance MPL.IO.instLawfulMonad {ε} : LawfulMonad (EIO ε) := _root_.IO.instLawfulMonad

open scoped MPL.IO in
noncomputable instance IO.instWPMonad : WPMonad (EIO ε) (.except ε .pure) where
  pure_pure := IO.wp_pure
  bind_bind := IO.wp_bind
