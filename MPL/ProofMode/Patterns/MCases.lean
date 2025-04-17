/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König
-/
import Lean.Data.Name

namespace MPL.ProofMode.Patterns
open Lean

declare_syntax_cat mcasesPat
syntax mcasesPatAlts := sepBy1(mcasesPat, " | ")
syntax binderIdent : mcasesPat
syntax "-" : mcasesPat
syntax "⟨" mcasesPatAlts,* "⟩" : mcasesPat
syntax "(" mcasesPatAlts ")" : mcasesPat
syntax "⌜" binderIdent "⌝" : mcasesPat
syntax "□" binderIdent : mcasesPat

macro "%" h:binderIdent : mcasesPat => `(mcasesPat| ⌜$h⌝)
macro "#" h:binderIdent : mcasesPat => `(mcasesPat| □ $h)

inductive MCasesPat
  | one (name : TSyntax ``binderIdent)
  | clear
  | tuple (args : List MCasesPat)
  | alts (args : List MCasesPat)
  | pure       (h : TSyntax ``binderIdent)
  | stateful (h : TSyntax ``binderIdent)
  deriving Repr, Inhabited

partial def MCasesPat.parse (pat : TSyntax `mcasesPat) : MacroM MCasesPat := do
  match go ⟨← expandMacros pat⟩ with
  | none => Macro.throwUnsupported
  | some pat => return pat
where
  go : TSyntax `mcasesPat → Option MCasesPat
  | `(mcasesPat| $name:binderIdent) => some <| .one name
  | `(mcasesPat| -) => some <| .clear
  | `(mcasesPat| ⟨$[$args],*⟩) => args.mapM goAlts |>.map (.tuple ·.toList)
  | `(mcasesPat| ⌜$h⌝) => some (.pure h)
  | `(mcasesPat| □$h) => some (.stateful h)
  | `(mcasesPat| ($pat)) => goAlts pat
  | _ => none
  goAlts : TSyntax ``mcasesPatAlts → Option MCasesPat
  | `(mcasesPatAlts| $args|*) =>
    match args.getElems with
    | #[arg] => go arg
    | args   => args.mapM go |>.map (.alts ·.toList)
  | _ => none
