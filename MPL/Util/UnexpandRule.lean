/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Sebastian Graf
-/
import Lean

namespace MPL.Util

open Lean Macro Parser

-- macro for adding unexpanders for function applications
private def matchAlts' := leading_parser Term.matchAlts

syntax "app_unexpand_rule" ident matchAlts' : command
macro_rules
  | `(app_unexpand_rule $f $[| $p => $s]*) => do
    let f := f.getId
    if f.isAnonymous then
      throwUnsupported
    let f ← match ← Macro.resolveGlobalName f with
      | [(name, [])] => pure name
      | _           => throwUnsupported

    let (p : TSyntaxArray `term) := p
    if p.any (· matches `(`($$_))) then
      `(@[app_unexpander $(mkIdent f)]
        def unexpand : Lean.PrettyPrinter.Unexpander
          $[| $p => $s]*)
    else
      `(@[app_unexpander $(mkIdent f)]
        def unexpand : Lean.PrettyPrinter.Unexpander
          $[| $p => $s]*
          | _ => throw ())
