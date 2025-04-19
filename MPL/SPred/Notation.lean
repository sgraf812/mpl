/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license.
Authors: Lars König, Sebastian Graf
-/

import Lean
import MPL.SPred.SPred
import MPL.Utils.UnexpandRule

namespace MPL.SPred.Notation

open Lean Macro Parser

-- define `spred` embedding in `term`.
-- An explicit `spred` marker avoids exponential blowup in terms
-- that do not opt into the extended syntax.
syntax:max "spred(" term ")" : term
syntax:max "term(" term ")" : term

-- allow fallback to `term`
macro_rules
  | `(spred(term($t))) => pure t
  | `(spred($t))       => pure t

-- push `spred` inside some `term` constructs
macro_rules
  | `(spred(($P)))                  => ``((spred($P)))
  | `(spred(fun $xs* => $b))        => ``(fun $xs* => spred($b))
  | `(spred(if $c then $t else $e)) => ``(if $c then spred($t) else spred($e))
  | `(spred(($P : $t)))             => ``((spred($P) : $t))

/-- Remove an `spred` layer from a `term` syntax object. -/
-- inverts the rules above.
partial def unpack [Monad m] [MonadRef m] [MonadQuotation m] : Term → m Term
  | `(spred($P))             => do `($P)
  | `(($P))                  => do `(($(← unpack P)))
  | `(if $c then $t else $e) => do
    let t ← unpack t
    let e ← unpack e
    `(if $c then $t else $e)
  | `(fun $xs* => $b)        => do
    let b ← unpack b
    `(fun $xs* => $b)
  | `(($P : $t))             => do ``(($(← unpack P) : $t))
  | `($t)                    => `($t)

-- `SVal` idiom notation.
/-- Start an idiom notation block (`SVal.idiom`).
This will capture the state tuple of the ambient `SVal`
and makes it available in pure expressions through `#t` notation. -/
syntax:lead "Ⓢ" term:lead : term
/-- Syntax for `SVal.pure` to embed pure values into `SVal`. -/
syntax "⌜" term "⌝" : term
/-- Use state tuple selector `t` in `SVal` idiom notation.
Implemented by `SVal.uncurry t (by assumption)`. -/
syntax:max "#" term:max : term
/-- Like ‹t› in `SVal`, but selects the state variable with
corresponding type from the ambient state tuple. -/
syntax "‹" term "›ₛ" : term

-- Now the actual logic.
/-- Entailment in `SPred`. -/
syntax:25 term:26 " ⊢ₛ " term:25 : term
/-- Tautology in `SPred`. -/
syntax:25 "⊢ₛ " term:25 : term
/-- Bi-entailment in `SPred`. -/
syntax:25 term:25 " ⊣⊢ₛ " term:25 : term

macro_rules
  | `(Ⓢ $t) => ``(SVal.idiom (fun _ => spred($t)))
  | `(⌜$t⌝) => ``(SVal.pure ($t))
  | `(#$t) => `(SVal.uncurry $t (by assumption))
  | `(‹$t›ₛ) => `(#(SVal.getThe $t))
  | `($P ⊢ₛ $Q) => ``(SPred.entails spred($P) spred($Q))
  | `(spred($P ∧ $Q)) => ``(SPred.and spred($P) spred($Q))
  | `(spred($P ∨ $Q)) => ``(SPred.or spred($P) spred($Q))
  | `(spred(¬ $P)) => ``(SPred.not spred($P))
  | `(spred($P → $Q)) => ``(SPred.imp spred($P) spred($Q))
  | `(spred($P ↔ $Q)) => ``(SPred.iff spred($P) spred($Q))
  | `(spred(∃ $xs:explicitBinders, $P)) => do expandExplicitBinders ``SPred.exists xs (← `(spred($P)))
  | `(⊢ₛ $P) => ``(⌜True⌝ ⊢ₛ $P)
  | `($P ⊣⊢ₛ $Q) => ``(SPred.bientails spred($P) spred($Q))
  -- Sadly, ∀ does not resently use expandExplicitBinders...
  | `(spred(∀ _%$tk, $P)) => ``(SPred.forall (fun _%$tk => spred($P)))
  | `(spred(∀ _%$tk : $ty, $P)) => ``(SPred.forall (fun _%$tk : $ty => spred($P)))
  | `(spred(∀ (_%$tk $xs* : $ty), $P)) => ``(SPred.forall (fun _%$tk : $ty => spred(∀ ($xs* : $ty), $P)))
  | `(spred(∀ $x:ident, $P)) => ``(SPred.forall (fun $x => spred($P)))
  | `(spred(∀ ($x:ident : $ty), $P)) => ``(SPred.forall (fun $x : $ty => spred($P)))
  | `(spred(∀ ($x:ident $xs* : $ty), $P)) => ``(SPred.forall (fun $x : $ty => spred(∀ ($xs* : $ty), $P)))
  | `(spred(∀ $x:ident $xs*, $P)) => ``(SPred.forall (fun $x => spred(∀ $xs*, $P)))
  | `(spred(∀ ($x:ident : $ty) $xs*, $P)) => ``(SPred.forall (fun $x : $ty => spred(∀ $xs*, $P)))
  | `(spred(∀ ($x:ident $xs* : $ty) $ys*, $P)) => ``(SPred.forall (fun $x : $ty => spred(∀ ($xs* : $ty) $ys*, $P)))

private abbrev theNat : SVal [Nat, Bool] Nat := fun n b => n
example (P Q : SPred [Nat, Bool]): SPred [Char, Nat, Bool] :=
  spred(fun c => ((∀ y, if y = 4 then Ⓢ⌜y = #theNat⌝ ∧ P else Q) ∧ Q) → (∃ x, P → if (x : Bool) then Q else P))

#check fun P Q => spred(fun n => ((∀ y, if y = n then P else Q) ∧ Q) → P → (∃ x, P → if (x : Bool) then Q else P))
#check fun P Q => spred(fun n => ((∀ y, if y = n then Ⓢ⌜‹Nat›ₛ = 4⌝ else Q) ∧ Q) → P → (∃ x, P → if (x : Bool) then Q else P))

app_unexpand_rule SPred.entails
  | `($_ $P $Q)  => do
    let P ← unpack P; let Q ← unpack Q;
    match P with
    | `(⌜True⌝) => ``(⊢ₛ $Q)
    | _ => ``($P ⊢ₛ $Q)
app_unexpand_rule SPred.bientails
  | `($_ $P $Q)  => do
    let P ← unpack P; let Q ← unpack Q;
    ``($P ⊣⊢ₛ $Q)
app_unexpand_rule SVal.pure
  | `($_ $t $ts*) => if ts.isEmpty then ``(⌜$t⌝) else ``(⌜$t⌝ $ts*)
app_unexpand_rule SVal.idiom
  | `($_ $t $ts*) => do
    match t with
    | `(fun $_ => $e) => if ts.isEmpty then ``(Ⓢ$e) else ``((Ⓢ$e) $ts*)
    | _ => throw ()
app_unexpand_rule SVal.uncurry
  | `($_ $f $_) => do
    match f with
    | `(SVal.getThe $t) => ``(‹$t›ₛ)
    | t => ``(#$t)
app_unexpand_rule SPred.and
  | `($_ $P $Q) => do
    let P ← unpack P; let Q ← unpack Q;
    ``(spred($P ∧ $Q))
app_unexpand_rule SPred.or
  | `($_ $P $Q) => do
    let P ← unpack P; let Q ← unpack Q;
    ``(spred($P ∨ $Q))
app_unexpand_rule SPred.not
  | `($_ $P) => do
    let P ← unpack P;
    ``(spred(¬ $P))
app_unexpand_rule SPred.imp
  | `($_ $P $Q) => do
    let P ← unpack P; let Q ← unpack Q;
    ``(spred($P → $Q))
app_unexpand_rule SPred.forall
  | `($_ fun $x:ident => ∀ $y:ident $[$z:ident]*, $Ψ) => do
    let Ψ ← unpack Ψ
    ``(spred(∀ $x:ident $y:ident $[$z:ident]*, $Ψ))
  | `($_ fun $x:ident => $Ψ) => do
    let Ψ ← unpack Ψ
    ``(spred(∀ $x:ident, $Ψ))
app_unexpand_rule SPred.exists
  | `($_ fun $x:ident => ∃ $y:ident $[$z:ident]*, $Ψ) => do
    let Ψ ← unpack Ψ
    ``(spred(∃ $x:ident $y:ident $[$z:ident]*, $Ψ))
  | `($_ fun $x:ident => $Ψ) => do
    let Ψ ← unpack Ψ
    ``(spred(∃ $x:ident, $Ψ))
app_unexpand_rule SPred.iff
  | `($_ $P $Q) => do
    let P ← unpack P; let Q ← unpack Q;
    ``(spred($P ↔ $Q))

#check fun P Q => spred(fun n => ((∀ y, if y = n then P else ⌜True⌝) ∧ Q) → P → (∃ x, P → if (x : Bool) then Q else P))
#check fun P Q => spred(fun n => ((∀ y, if y = n then Ⓢ⌜‹Nat›ₛ + #theNat = 4⌝ else Q) ∧ Q) → P → (∃ x, P → if (x : Bool) then Q else P))
-- Unexpansion should work irrespective of binder name for `f`/`escape`:
#check ∀ (a b n o : Nat) (s : Nat × Nat), (SVal.idiom fun f => ⌜a = n ∧ b = o⌝) ⊢ₛ SVal.idiom fun f => ⌜s.1 = n ∧ a = n + 1 ∧ b = o⌝
