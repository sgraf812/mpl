/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
import Lean
import MPL.SimpAttr

/-!
# Tactic `wp_simp`

The `simp` tactic `wp_simp` defined here is the basis for rewriting expressions of the form
`wp⟦x⟧.apply Q`.

This tactic will be superceded by a more sophisticated verification condition generator in the
future. The main difference would be that the VC generator would apply general Hoare triple
specifications (which can be lossy) instead of information preserving rewrites.
-/

namespace MPL

open Lean Parser Meta Elab Tactic

my_register_simp_attr wp_simp

def getWPSimpTheorems : CoreM SimpTheorems :=
  wp_simp_ext.getTheorems

/--
The `wp_simp` tactic is the basis for rewriting expressions of the form `wp⟦x⟧.apply Q`.

It is likely that this tactic will be superceded by a more sophisticated verification condition
generator in the future. The main difference would be that the VC generator would apply general
Hoare triple specifications (which can be lossy) instead of information preserving rewrites.
-/
syntax (name := wp_simp) "wp_simp" optConfig (discharger)? (&" only")?
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")? (location)? : tactic

@[tactic wp_simp] def evalWPSimp : Tactic := fun stx => withMainContext do withSimpDiagnostics do
  let { ctx, simprocs, dischargeWrapper } ← mkSimpContext stx (eraseLocal := false) (simpTheorems := getWPSimpTheorems)
  let stats ← dischargeWrapper.with fun discharge? =>
    simpLocation ctx simprocs discharge? (expandOptLocation stx[5])
  if tactic.simp.trace.get (← getOptions) then
    traceSimpCall stx stats.usedTheorems
  return stats.diag
