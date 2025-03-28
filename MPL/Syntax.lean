import Lean

namespace MPL

/-- A Proposition indexed by a list of states. -/
def σProp (σs : List Type) : Type := σs.foldr (fun σ P => σ → P) Prop

@[reducible]
def σProp.pure {σs : List Type} (P : Prop) : σProp σs := match σs with
| [] => P
| σ :: _ => fun (_ : σ) => pure P

@[reducible]
def σProp.entails {σs : List Type} (P Q : σProp σs) : Prop := match σs with
| [] => P → Q
| σ :: _ => ∀ (s : σ), entails (P s) (Q s)

@[reducible]
def σProp.exists {σs : List Type} (P Q : σProp σs) : σProp σs := match σs with
| [] => P ∧ Q
| σ :: _ => fun (s : σ) => and (P s) (Q s)

@[reducible]
def σProp.and {σs : List Type} (P Q : σProp σs) : σProp σs := match σs with
| [] => P ∧ Q
| σ :: _ => fun (s : σ) => and (P s) (Q s)

@[reducible]
def σProp.or {σs : List Type} (P Q : σProp σs) : σProp σs := match σs with
| [] => P ∨ Q
| σ :: _ => fun (s : σ) => or (P s) (Q s)

@[reducible]
def σProp.imp {σs : List Type} (P Q : σProp σs) : σProp σs := match σs with
| [] => P → Q
| σ :: _ => fun (s : σ) => imp (P s) (Q s)

@[reducible]
def σProp.iff {σs : List Type} (P Q : σProp σs) : σProp σs := and (imp P Q) (imp Q P)

declare_syntax_cat σprop

open Lean Parser Term in
def σpropBasicFun : Parser := leading_parser
  ppGroup (many1 (ppSpace >> funBinder) >> optType >> unicodeSymbol " ↦" " =>") >> ppSpace >> categoryParser `σprop 0

-- define `σprop` embedding in `term`
syntax:max "σprop(" σprop ")" : term

syntax:max "term(" term ")" : σprop
syntax:max "(" σprop ")" : σprop
syntax:max ident : σprop
syntax:max "?" ident : σprop
syntax:80 σprop:80 term:81 : σprop
syntax:lead "fun " σpropBasicFun : σprop
@[inherit_doc ite] syntax (name := ipropIfThenElse)
  ppRealGroup(ppRealFill(ppIndent("if " term " then") ppSpace σprop)
    ppDedent(ppSpace) ppRealFill("else " σprop)) : σprop
syntax:min σprop " : " term : σprop

-- Now the actual logic.
/-- Embedding of pure Lean proposition as separation logic proposition. -/
syntax "⌜" term "⌝" : σprop
/-- Conjunction in σProp. -/
syntax:35 σprop:36 " ∧ " σprop:35 : σprop
/-- Disjunction in σProp. -/
syntax:35 σprop:36 " ∨ " σprop:35 : σprop
/-- Implication in σProp. -/
syntax:25 σprop:26 " → " σprop:25 : σprop
/-- Bidirectional implication in σProp. -/
syntax:20 σprop:21 " ↔ " σprop:21 : σprop
/-- Entailment in σProp. -/
syntax:25 σprop:26 " → " σprop:25 : σprop

macro_rules
  | `(σprop(term($t))) => pure t
  | `(σprop(($P))) => ``((σprop($P)))
  | `(σprop($x:ident)) => ``($x)
  | `(σprop(?$x:ident)) => ``(?$x)
  | `(σprop($P $Q)) => ``(σprop($P) $Q)
  | `(σprop(fun $[$bs]* $[: $ty]? => $p)) => ``(fun $bs* $[: $ty]? => σprop($p))
  | `(σprop(if $c then $t else $e)) => ``(if $c then σprop($t) else σprop($e))
  | `(σprop($P : $t)) => ``((σprop($P) : $t))

  | `(σprop(⌜$t⌝)) => ``(σProp.pure $t)
  | `(σprop($P ∧ $Q)) => ``(σProp.and σprop($P) σprop($Q))
  | `(σprop($P ∨ $Q)) => ``(σProp.or σprop($P) σprop($Q))
  | `(σprop($P → $Q)) => ``(σProp.imp σprop($P) σprop($Q))
  | `(σprop($P ↔ $Q)) => ``(σProp.iff σprop($P) σprop($Q))

def test (P Q : σProp [Bool]): σProp [Nat, Bool] := σprop(fun n b => (P b ∧ Q b) → (P b → Q b))
#print test
