import Lean.Data.Name

namespace MPL.ProofMode.Patterns
open Lean

declare_syntax_cat srefinePat
syntax binderIdent : srefinePat
syntax srefinePats := sepBy1(srefinePat, ", ")
syntax "⟨" srefinePats "⟩" : srefinePat
syntax "(" srefinePat ")" : srefinePat
syntax "⌜" term "⌝" : srefinePat
syntax "□" binderIdent : srefinePat
syntax "?" binderIdent : srefinePat

macro "%" h:term : srefinePat => `(srefinePat| ⌜$h⌝)
macro "#" h:binderIdent : srefinePat => `(srefinePat| □ $h)

inductive SRefinePat
  | one (name : TSyntax ``binderIdent)
  | tuple (args : List SRefinePat)
  | pure       (h : TSyntax `term)
  | persistent (h : TSyntax ``binderIdent)
  | hole (name : TSyntax ``binderIdent)
  deriving Repr, Inhabited

partial def SRefinePat.parse (pat : TSyntax `srefinePat) : MacroM SRefinePat := do
  match go ⟨← expandMacros pat⟩ with
  | none => Macro.throwUnsupported
  | some pat => return pat
where
  go : TSyntax `srefinePat → Option SRefinePat
  | `(srefinePat| $name:binderIdent) => some <| .one name
  | `(srefinePat| ?$name) => some (.hole name)
  | `(srefinePat| ⟨$[$args],*⟩) => args.mapM go |>.map (.tuple ·.toList)
  | `(srefinePat| ⌜$h⌝) => some (.pure h)
  | `(srefinePat| □$h) => some (.persistent h)
  | `(srefinePat| ($pat)) => go pat
  | _ => none
