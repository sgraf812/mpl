import Lean
import MPL.SProp.Basic

section Delab
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

end Delab

namespace MPL

open Lean Macro Parser

-- define `sprop` embedding in `term`.
-- An explicit `sprop` marker avoids exponential blowup in terms
-- that do not opt into the extended syntax.
syntax:max "sprop(" term ")" : term
syntax:max "term(" term ")" : term

-- allow fallback to `term`
macro_rules
  | `(sprop(term($t))) => pure t
  | `(sprop($t))       => pure t

-- push `sprop` inside some `term` constructs
macro_rules
  | `(sprop(($P)))                  => ``((sprop($P)))
  | `(sprop(fun $xs* => $b))        => ``(fun $xs* => sprop($b))
  | `(sprop(if $c then $t else $e)) => ``(if $c then sprop($t) else sprop($e))
  | `(sprop(($P : $t)))             => ``((sprop($P) : $t))

/-- Remove an `sprop` layer from a `term` syntax object. -/
-- inverts the rules above.
partial def unpackSprop [Monad m] [MonadRef m] [MonadQuotation m] : Term → m Term
  | `(sprop($P))             => do `($P)
  | `(($P))                  => do `(($(← unpackSprop P)))
  | `(if $c then $t else $e) => do
    let t ← unpackSprop t
    let e ← unpackSprop e
    `(if $c then $t else $e)
  | `(fun $xs* => $b)        => do
    let b ← unpackSprop b
    `(fun $xs* => $b)
  | `(($P : $t))             => do ``(($(← unpackSprop P) : $t))
  | `($t)                    => `($t)

-- Now the actual logic.
/-- Embedding of pure Lean propositions into `SProp`. -/
syntax "⌜" term "⌝" : term
/-- Entailment in `SProp`. -/
syntax:25 term:26 " ⊢ₛ " term:25 : term
/-- ‹t› in `SProp`. -/
syntax "‹" term "›ₛ" : term
/-- Use getter `t` in `SProp` idiom notation. -/
syntax:max "#" term:max : term

macro_rules
  | `($P ⊢ₛ $Q) => ``(SProp.entails sprop($P) sprop($Q))
  | `(sprop($P ∧ $Q)) => ``(SProp.and sprop($P) sprop($Q))
  | `(sprop($P ∨ $Q)) => ``(SProp.or sprop($P) sprop($Q))
  | `(sprop($P → $Q)) => ``(SProp.imp sprop($P) sprop($Q))
  | `(sprop($P ↔ $Q)) => ``(SProp.iff sprop($P) sprop($Q))
  | `(sprop(∀ $x:ident, $P)) => ``(SProp.forall (fun $x => sprop($P)))
  | `(sprop(∀ $x:ident $xs*, $P)) => ``(SProp.forall (fun $x => sprop(∀ $xs*, $P)))
  | `(sprop(∃ $x:ident, $P)) => ``(SProp.exists (fun $x => sprop($P)))
  | `(sprop(exists $x:ident, $P)) => ``(SProp.exists (fun $x => sprop($P)))
  | `(⌜$t⌝) => ``(SProp.idiom (fun escape => $t))
  | `(#$t) => `(SVal.GetTy.applyEscape $t (by assumption))
  | `(‹$t›ₛ) => `(#(SVal.getThe $t))

def theNat : SVal [Nat, Bool] Nat := fun n b => n
example (P Q : SProp [Nat, Bool]): SProp [Char, Nat, Bool] :=
  sprop(fun c => ((∀ y, if y = 4 then ⌜y = #theNat⌝ ∧ P else Q) ∧ Q) → (∃ x, P → if (x : Bool) then Q else P))

#check fun P Q => sprop(fun n => ((∀ y, if y = n then P else Q) ∧ Q) → P → (∃ x, P → if (x : Bool) then Q else P))
#check fun P Q => sprop(fun n => ((∀ y, if y = n then ⌜‹Nat›ₛ = 4⌝ else Q) ∧ Q) → P → (∃ x, P → if (x : Bool) then Q else P))

app_unexpand_rule SProp.entails
  | `($_ $P $Q)  => do
    let P ← unpackSprop P; let Q ← unpackSprop Q;
    ``($P ⊢ₛ $Q)
app_unexpand_rule SProp.idiom
  | `($_ $t $ts*) => do
    match t with
    | `(fun escape => $e) => ``(⌜$e⌝)
    | _ => throw ()
app_unexpand_rule SVal.GetTy.applyEscape
  | `($_ $f $_) => do
    match f with
    | `(SVal.getThe $t) => ``(‹$t›ₛ)
    | t => ``(#$t)
app_unexpand_rule SProp.and
  | `($_ $P $Q) => do
    let P ← unpackSprop P; let Q ← unpackSprop Q;
    ``(sprop($P ∧ $Q))
app_unexpand_rule SProp.or
  | `($_ $P $Q) => do
    let P ← unpackSprop P; let Q ← unpackSprop Q;
    ``(sprop($P ∨ $Q))
app_unexpand_rule SProp.imp
  | `($_ $P $Q) => do
    let P ← unpackSprop P; let Q ← unpackSprop Q;
    ``(sprop($P → $Q))
app_unexpand_rule SProp.forall
  | `($_ fun $x:ident => ∀ $y:ident $[$z:ident]*, $Ψ) => do
    let Ψ ← unpackSprop Ψ
    ``(sprop(∀ $x:ident $y:ident $[$z:ident]*, $Ψ))
  | `($_ fun $x:ident => $Ψ) => do
    let Ψ ← unpackSprop Ψ
    ``(sprop(∀ $x:ident, $Ψ))
app_unexpand_rule SProp.exists
  | `($_ fun $x:ident => ∃ $y:ident $[$z:ident]*, $Ψ) => do
    let Ψ ← unpackSprop Ψ
    ``(sprop(∃ $x:ident $y:ident $[$z:ident]*, $Ψ))
  | `($_ fun $x:ident => $Ψ) => do
    let Ψ ← unpackSprop Ψ
    ``(sprop(∃ $x:ident, $Ψ))
app_unexpand_rule SProp.iff
  | `($_ $P $Q) => do
    let P ← unpackSprop P; let Q ← unpackSprop Q;
    ``(sprop($P ↔ $Q))

#check fun P Q => sprop(fun n => ((∀ y, if y = n then P else ⌜True⌝) ∧ Q) → P → (∃ x, P → if (x : Bool) then Q else P))
#check fun P Q => sprop(fun n => ((∀ y, if y = n then ⌜4 = ‹Nat›ₛ⌝ else Q) ∧ Q) → P → (∃ x, P → if (x : Bool) then Q else P))
#check fun P Q => sprop(fun n => ((∀ y, if y = n then ⌜‹Nat›ₛ + ‹Nat›ₛ = 4⌝ else Q) ∧ Q) → P → (∃ x, P → if (x : Bool) then Q else P))
#check fun P Q => sprop(fun n => ((∀ y, if y = n then ⌜‹Nat›ₛ + #theNat = 4⌝ else Q) ∧ Q) → P → (∃ x, P → if (x : Bool) then Q else P))
