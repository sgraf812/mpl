/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König
-/
import Lean.Data.Name

namespace MPL.ProofMode.Patterns
open Lean

declare_syntax_cat scasesPat
syntax scasesPatAlts := sepBy1(scasesPat, " | ")
syntax binderIdent : scasesPat
syntax "-" : scasesPat
syntax "⟨" scasesPatAlts,* "⟩" : scasesPat
syntax "(" scasesPatAlts ")" : scasesPat
syntax "⌜" binderIdent "⌝" : scasesPat
syntax "□" binderIdent : scasesPat

macro "%" h:binderIdent : scasesPat => `(scasesPat| ⌜$h⌝)
macro "#" h:binderIdent : scasesPat => `(scasesPat| □ $h)

inductive SCasesPat
  | one (name : TSyntax ``binderIdent)
  | clear
  | tuple (args : List SCasesPat)
  | alts (args : List SCasesPat)
  | pure       (h : TSyntax ``binderIdent)
  | persistent (h : TSyntax ``binderIdent)
  deriving Repr, Inhabited

partial def SCasesPat.parse (pat : TSyntax `scasesPat) : MacroM SCasesPat := do
  match go ⟨← expandMacros pat⟩ with
  | none => Macro.throwUnsupported
  | some pat => return pat
where
  go : TSyntax `scasesPat → Option SCasesPat
  | `(scasesPat| $name:binderIdent) => some <| .one name
  | `(scasesPat| -) => some <| .clear
  | `(scasesPat| ⟨$[$args],*⟩) => args.mapM goAlts |>.map (.tuple ·.toList)
  | `(scasesPat| ⌜$h⌝) => some (.pure h)
  | `(scasesPat| □$h) => some (.persistent h)
  | `(scasesPat| ($pat)) => goAlts pat
  | _ => none
  goAlts : TSyntax ``scasesPatAlts → Option SCasesPat
  | `(scasesPatAlts| $args|*) =>
    match args.getElems with
    | #[arg] => go arg
    | args   => args.mapM go |>.map (.alts ·.toList)
  | _ => none
