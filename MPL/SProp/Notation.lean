import Lean
import MPL.SProp.Basic

section Delab
open Lean Macro Parser

-- macro for adding unexpanders for function applications
private def matchAlts' := leading_parser Term.matchAlts

syntax "delab_rule" ident matchAlts' : command
macro_rules
  | `(delab_rule $f $[| $p => $s]*) => do
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

end Delab

namespace MPL

declare_syntax_cat sprop

open Lean Macro Parser

def spropBasicFun : Parser := leading_parser
  ppGroup (many1 (ppSpace >> Term.funBinder) >> Term.optType >> unicodeSymbol " ↦" " =>") >> ppSpace >> categoryParser `sprop 0

def spropForall := leading_parser:leadPrec
  unicodeSymbol "∀" "forall" >>
  many1 (ppSpace >> (Term.binderIdent <|> Term.bracketedBinder)) >>
  Term.optType >> ", " >> categoryParser `sprop 0

-- define `sprop` embedding in `term`
syntax:max "sprop(" sprop ")" : term

syntax:max "term(" term ")" : sprop
syntax:max "(" sprop ")" : sprop
syntax:max ident : sprop
syntax:max "?" ident : sprop
syntax:80 sprop:80 term:81 : sprop
syntax:lead "fun " spropBasicFun : sprop
@[inherit_doc ite] syntax (name := ipropIfThenElse)
  ppRealGroup(ppRealFill(ppIndent("if " term " then") ppSpace sprop)
    ppDedent(ppSpace) ppRealFill("else " sprop)) : sprop
syntax:min sprop " : " term : sprop

-- Now the actual logic.
/-- Embedding of pure Lean propositions. -/
syntax "⌜" term "⌝" : sprop
/-- Conjunction in SProp. -/
syntax:35 sprop:36 " ∧ " sprop:35 : sprop
/-- Disjunction in SProp. -/
syntax:35 sprop:36 " ∨ " sprop:35 : sprop
/-- Implication in SProp. -/
syntax:25 sprop:26 " → " sprop:25 : sprop
/-- Bidirectional implication in SProp. -/
syntax:20 sprop:21 " ↔ " sprop:21 : sprop
/-- Entailment in SProp. -/
syntax:25 sprop:26 " → " sprop:25 : sprop
/-- Disjunction in SProp. -/
syntax:35 sprop:36 " ∨ " sprop:35 : sprop
/-- Universal quantification in SProp. -/
syntax:lead spropForall : sprop
/-- Existential quantification in SProp. -/
syntax "∃" explicitBinders ", " sprop : sprop
syntax "exists" explicitBinders ", " sprop : sprop
/-- ‹t› in sprop -/
syntax "‹" term "› " : sprop

-- /-- Entailment predicate on indexed propositions. -/
-- syntax:25 sprop:29 " ⊢ " sprop:25 : term
-- macro_rules
--   | `($P:sprop ⊢ $Q:sprop) => ``(SProp.entails sprop($P) sprop($Q))

macro_rules
  | `(sprop(term($t))) => pure t
  | `(sprop(($P))) => ``((sprop($P)))
  | `(sprop($x:ident)) => ``($x)
  | `(sprop(?$x:ident)) => ``(?$x)
  | `(sprop($P $Q)) => ``(sprop($P) $Q)
  | `(sprop(fun $[$bs]* $[: $ty]? => $p)) => ``(fun $bs* $[: $ty]? => sprop($p))
  | `(sprop(if $c then $t else $e)) => ``(if $c then sprop($t) else sprop($e))
  | `(sprop($P : $t)) => ``((sprop($P) : $t))

  | `(sprop(⌜$t⌝)) => ``(SProp.pure $t)
  | `(sprop($P ∧ $Q)) => ``(SProp.and sprop($P) sprop($Q))
  | `(sprop($P ∨ $Q)) => ``(SProp.or sprop($P) sprop($Q))
  | `(sprop($P → $Q)) => ``(SProp.imp sprop($P) sprop($Q))
  | `(sprop($P ↔ $Q)) => ``(SProp.iff sprop($P) sprop($Q))
  | `(sprop(∀ $x:ident, $P)) => ``(SProp.forall (fun $x => sprop($P)))
  | `(sprop(∀ $x:ident $xs*, $P)) => ``(SProp.forall (fun $x => sprop(∀ $xs*, $P)))
--  | `(sprop(∀ $x: $xs*, $P)) => ``(SProp.forall (fun $x => sprop(∀ $xs*, $P $x))) -- urgh
  | `(sprop(∃ $x:ident, $P)) => ``(SProp.exists (fun $x => sprop($P))) -- TODO: support multiple binders

example (P Q : SProp [Bool]): SProp [Nat, Bool] :=
  sprop(fun n => ((∀ y, if y = n then P else Q) ∧ Q) → (∃ x, P → if (x : Bool) then Q else P))

/-- Remove an `sprop` quotation from a `term` syntax object. -/
partial def unpacksprop [Monad m] [MonadRef m] [MonadQuotation m] : Term → m (TSyntax `sprop)
  | `(sprop($P))             => do `(sprop|$P)
  | `($x:ident)              => do `(sprop|$x:ident)
  | `(?$x:ident)             => do `(sprop|?$x:ident)
  | `(($P))                  => do `(sprop|$(← unpacksprop P))
  | `($P $Q)                 => do `(sprop|$(← unpacksprop P) $Q)
  | `(fun $[$bs]* $[: $ty]? => $p) => do `(sprop|fun $[$bs]* $[: $ty]? => $(← unpacksprop p))
  | `(if $c then $t else $e) => do `(sprop|if $c then $(← unpacksprop t) else $(← unpacksprop e))
  | `(($P : $t))             => do `(sprop|$(← unpacksprop P) : $t)

  | `($P ∧ $Q)               => do `(sprop|$(← unpacksprop P) ∧ $(← unpacksprop Q))
  | `(∀x, $P ∧ $Q)           => do `(sprop|$(← unpacksprop P) ∧ $(← unpacksprop Q))
  | `($P ∨ $Q)               => do `(sprop|$(← unpacksprop P) ∨ $(← unpacksprop Q))
  | `(∀x, $P ∨ $Q)           => do `(sprop|$(← unpacksprop P) ∨ $(← unpacksprop Q))
  | `($P → $Q)              => do `(sprop|$(← unpacksprop P) → $(← unpacksprop Q))
  | `(∀x, $P → $Q)          => do `(sprop|$(← unpacksprop P) → $(← unpacksprop Q))
  | `($P ↔ $Q)              => do `(sprop|$(← unpacksprop P) ↔ $(← unpacksprop Q))
  | `(∀x, $P ↔ $Q)          => do `(sprop|$(← unpacksprop P) ↔ $(← unpacksprop Q))
  | t                        => do `(sprop|⌜$t:term⌝)

/-
delab_rule SProp.pure
  | `($_ $φ) => ``(sprop(⌜$φ⌝))
delab_rule SProp.and
  | `($_ $P $Q) => do ``(sprop($(← unpacksprop P) ∧ $(← unpacksprop Q)))
delab_rule SProp.or
  | `($_ $P $Q) => do ``(sprop($(← unpacksprop P) ∨ $(← unpacksprop Q)))
delab_rule SProp.imp
  | `($_ $P $Q) => do ``(sprop($(← unpacksprop P) → $(← unpacksprop Q)))
delab_rule SProp.forall
  | `($_ fun $x:ident => sprop(∀ $y:ident $[$z:ident]*, $Ψ)) => do
    ``(sprop(∀ $x:ident $y:ident $[$z:ident]*, $Ψ))
  | `($_ fun $x:ident => $Ψ) => do ``(sprop(∀ $x:ident, $(← unpacksprop Ψ)))
delab_rule SProp.exists
  | `($_ fun $x:ident => sprop(∃ $y:ident $[$z:ident]*, $Ψ)) => do
    ``(sprop(∃ $x:ident $y:ident $[$z:ident]*, $Ψ))
  | `($_ fun $x:ident => $Ψ) => do ``(sprop(∃ $x:ident, $(← unpacksprop Ψ)))

delab_rule SProp.pure
  | `($_ True) => ``(sprop(SProp.pure True))
  | `($_ False) => ``(sprop(SProp.pure False))
delab_rule SProp.imp
  | `($_ $P sprop(False)) => do ``(sprop(SProp.imp $(← unpacksprop P) sprop(False)))
-/
