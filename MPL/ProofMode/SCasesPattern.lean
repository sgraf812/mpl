/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König
-/
import Lean.Data.Name

namespace MPL.ProofMode
open Lean

declare_syntax_cat scasesPat
syntax scasesPatAlts := sepBy1(scasesPat, " | ")
syntax binderIdent : scasesPat
syntax "-" : scasesPat
syntax "⟨" scasesPatAlts,* "⟩" : scasesPat
syntax "(" scasesPatAlts ")" : scasesPat
syntax "⌜" scasesPat "⌝" : scasesPat
syntax "□" scasesPat : scasesPat

macro "%" pat:scasesPat : scasesPat => `(scasesPat| ⌜$pat⌝)
macro "#" pat:scasesPat : scasesPat => `(scasesPat| □ $pat)

inductive SCasesPat
  | one (name : TSyntax ``binderIdent)
  | clear
  | conjunction (args : List SCasesPat)
  | disjunction (args : List SCasesPat)
  | pure       (pat : SCasesPat)
  | persistent (pat : SCasesPat)
  deriving Repr, Inhabited

partial def SCasesPat.parse (pat : TSyntax `scasesPat) : MacroM SCasesPat := do
  match go ⟨← expandMacros pat⟩ with
  | none => Macro.throwUnsupported
  | some pat => return pat
where
  go : TSyntax `scasesPat → Option SCasesPat
  | `(scasesPat| $name:binderIdent) => some <| .one name
  | `(scasesPat| -) => some <| .clear
  | `(scasesPat| ⟨$[$args],*⟩) => args.mapM goAlts |>.map (.conjunction ·.toList)
  | `(scasesPat| ⌜$pat⌝) => go pat |>.map .pure
  | `(scasesPat| □$pat) => go pat |>.map .persistent
  | `(scasesPat| ($pat)) => goAlts pat
  | _ => none
  goAlts : TSyntax ``scasesPatAlts → Option SCasesPat
  | `(scasesPatAlts| $args|*) =>
    match args.getElems with
    | #[arg] => go arg
    | args   => args.mapM go |>.map (.disjunction ·.toList)
  | _ => none
