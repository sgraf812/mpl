/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
import Lean
import MPL.SimpAttr

namespace MPL

open Lean Parser Meta Elab Tactic

my_register_simp_attr wp_simp

def getWPSimpTheorems : CoreM SimpTheorems :=
  wp_simp_ext.getTheorems

syntax (name := wp_simp) "wp_simp" optConfig (discharger)? (&" only")?
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")? (location)? : tactic

@[tactic wp_simp] def evalWPSimp : Tactic := fun stx => withMainContext do withSimpDiagnostics do
  let { ctx, simprocs, dischargeWrapper } ← mkSimpContext stx (eraseLocal := false) (simpTheorems := getWPSimpTheorems)
  let stats ← dischargeWrapper.with fun discharge? =>
    simpLocation ctx simprocs discharge? (expandOptLocation stx[5])
  if tactic.simp.trace.get (← getOptions) then
    traceSimpCall stx stats.usedTheorems
  return stats.diag
