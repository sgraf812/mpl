/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
import Lean.Data.Name

namespace MPL.ProofMode.Patterns
open Lean

declare_syntax_cat mrefinePat
syntax binderIdent : mrefinePat
syntax mrefinePats := sepBy1(mrefinePat, ", ")
syntax "⟨" mrefinePats "⟩" : mrefinePat
syntax "(" mrefinePat ")" : mrefinePat
syntax "⌜" term "⌝" : mrefinePat
syntax "□" binderIdent : mrefinePat
syntax "?" binderIdent : mrefinePat

macro "%" h:term : mrefinePat => `(mrefinePat| ⌜$h⌝)
macro "#" h:binderIdent : mrefinePat => `(mrefinePat| □ $h)

inductive MRefinePat
  | one (name : TSyntax ``binderIdent)
  | tuple (args : List MRefinePat)
  | pure       (h : TSyntax `term)
  | stateful (h : TSyntax ``binderIdent)
  | hole (name : TSyntax ``binderIdent)
  deriving Repr, Inhabited

partial def MRefinePat.parse (pat : TSyntax `mrefinePat) : MacroM MRefinePat := do
  match go ⟨← expandMacros pat⟩ with
  | none => Macro.throwUnsupported
  | some pat => return pat
where
  go : TSyntax `mrefinePat → Option MRefinePat
  | `(mrefinePat| $name:binderIdent) => some <| .one name
  | `(mrefinePat| ?$name) => some (.hole name)
  | `(mrefinePat| ⟨$[$args],*⟩) => args.mapM go |>.map (.tuple ·.toList)
  | `(mrefinePat| ⌜$h⌝) => some (.pure h)
  | `(mrefinePat| □$h) => some (.stateful h)
  | `(mrefinePat| ($pat)) => go pat
  | _ => none
