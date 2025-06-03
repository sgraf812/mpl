/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
import Lean
import MPL.Triple
import MPL.SpecAttr

import MPL.Specs
import MPL.WPMonad
import MPL.WPMonadLift
import MPL.WPMonadFunctor
import MPL.WPMonadExceptOf
import MPL.WPSimp
import MPL.SPred.ProofMode

namespace MPL

open Lean Meta Elab Tactic

syntax "crush_trivial" : tactic
macro_rules | `(tactic| crush_trivial) => `(tactic| trivial)

syntax (name := crush) "crush" optional("[" Lean.Parser.Tactic.simpLemma,+ "]") : tactic
macro_rules
  | `(tactic| crush) => `(tactic| crush[if_true_left]) -- if_true_left is redundant, but empty list did not work for some reason.
  | `(tactic| crush [$args,*]) => `(tactic| (intros; first
    | (intro; repeat intro) -- expand ≤ on → and Assertions, also turns triple goals into wp goals
    | crush_trivial
    | simp_all only [if_true_left, if_false_left, and_self, and_true, List.length_nil, List.length_cons, ne_eq, not_false_eq_true, gt_iff_lt
        , reduceIte
        , Nat.sub_one_add_one
        , SVal.curry_nil
        , PostCond.total
      ]
    | (simp_all [$args,*, Nat.sub_one_add_one]; done)
    -- | grind
    ))

end MPL
