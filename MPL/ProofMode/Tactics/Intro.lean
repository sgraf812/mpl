/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Sebastian Graf
-/
import MPL.ProofMode.Tactics.Basic
import MPL.ProofMode.Patterns.MCases
import MPL.ProofMode.Display

open Lean Elab Tactic Meta

namespace MPL.ProofMode.Tactics

declare_syntax_cat mintroPat
syntax mcasesPat : mintroPat
syntax "∀" binderIdent : mintroPat

theorem Intro.intro {σs : List Type} {P Q H T : SPred σs} (hand : Q ∧ H ⊣⊢ₛ P) (h : P ⊢ₛ T) : Q ⊢ₛ H → T :=
  SPred.imp_intro (hand.mp.trans h)

partial def mIntro (goal : MGoal) (ident : TSyntax ``binderIdent) (k : MGoal → MetaM Expr) : MetaM Expr := do
  let some (σs, H, T) := goal.target.app3? ``SPred.imp | throwError "Target not an implication {goal.target}"
  let (name, _ref) ← getFreshHypName ident
  let Q := goal.hyps
  let H := (Hyp.mk name H).toExpr
  let (P, hand) := mkAnd goal.σs goal.hyps H
  let prf ← k { goal with hyps := P, target := T }
  let prf := mkApp7 (mkConst ``Intro.intro) σs P Q H T hand prf
  return prf

-- This is regular MVar.intro, but it takes care not to leave the proof mode by preserving metadata
partial def mIntroForall (goal : MGoal) (ident : TSyntax ``binderIdent) (k : MGoal → MetaM Expr) : MetaM Expr := do
  let some (_type, σ, σs') := (← whnf goal.σs).app3? ``List.cons | throwError "Ambient state list not a cons {goal.σs}"
  let name ← match ident with
  | `(binderIdent| $name:ident) => pure name.getId
  | `(binderIdent| $_) => mkFreshUserName `s
  withLocalDeclD name σ fun s => do
    let H := betaRevPreservingHypNames σs' goal.hyps #[s]
    let T := goal.target.betaRev #[s]
    let prf ← mkLambdaFVars #[s] (← k { σs:=σs', hyps:=H, target:=T })
    return mkApp5 (mkConst ``SPred.entails_cons_intro) σ σs' goal.hyps goal.target prf

/--
  Like `rcases`, but operating on stateful hypotheses.
  Example: Given a goal `h : (P ∧ (Q ∨ R) ∧ (Q → R)) ⊢ₛ R`,
  `mcases h with ⟨-, ⟨hq | hr⟩, hqr⟩` will yield two goals:
  `(hq : Q, hqr : Q → R) ⊢ₛ R` and `(hr : R) ⊢ₛ R`.

  That is, `mcases h with pat` has the following semantics, based on `pat`:
  * `pat=□h'` renames `h` to `h'` in the stateful context, regardless of whether `h` is pure
  * `pat=⌜h'⌝` introduces `h' : φ`  to the pure local context if `h : ⌜φ⌝` (c.f. `IsPure`)
  * `pat=h'` is like `pat=⌜h'⌝` if `h` is pure (c.f. `IsPure`), otherwise it is like `pat=□h'`.
  * `pat=_` renames `h` to an inaccessible name
  * `pat=-` discards `h`
  * `⟨pat₁, pat₂⟩` matches on conjunctions and existential quantifiers and recurses via
    `pat₁` and `pat₂`.
  * `⟨pat₁ | pat₂⟩` matches on disjunctions, matching the left alternative via `pat₁` and the right
    alternative via `pat₂`.
-/
syntax (name := mcases) "mcases" colGt ident "with" colGt mcasesPat : tactic

/--
  Like `intro`, but introducing stateful hypotheses into the stateful context.
  That is, given a stateful goal `(hᵢ : Hᵢ)* ⊢ₛ P → T`, `mintro h` transforms
  intro `(hᵢ : Hᵢ)*, (h : P) ⊢ₛ T`.

  Furthermore, `mintro ∀s` is like `intro s`, but preserves the stateful goal.
  That is, `mintro ∀s` brings the topmost state variable `s:σ` in scope and transforms
  `(hᵢ : Hᵢ)* ⊢ₛ T` (where the entailment is in `SPred (σ::σs)`) into
  `(hᵢ : Hᵢ s)* ⊢ₛ T s` (where the entailment is in `SPred σs`).

  Beyond that, `mintro` supports the full syntax of `mcases` patterns
  (`mintro pat = (mintro h; mcases h with pat`), and can perform multiple
  introductions in sequence.
-/
syntax (name := mintro) "mintro" (colGt mintroPat)+ : tactic

macro_rules
  | `(tactic| mintro $pat₁ $pat₂ $pats:mintroPat*) => `(tactic| mintro $pat₁; mintro $pat₂ $pats*)
  | `(tactic| mintro $pat:mintroPat) => do
    match pat with
    | `(mintroPat| $_:binderIdent) => Macro.throwUnsupported -- handled by an elaborator below
    | `(mintroPat| ∀$_:binderIdent) => Macro.throwUnsupported -- handled by an elaborator below
    | `(mintroPat| $pat:mcasesPat) => `(tactic| mintro h; mcases h with $pat)
    | _ => Macro.throwUnsupported -- presently unreachable

elab_rules : tactic
  | `(tactic| mintro $ident:binderIdent) => do

  let (mvar, goal) ← mStart (← getMainGoal)
  mvar.withContext do

  let goals ← IO.mkRef []
  mvar.assign (← mIntro goal ident fun newGoal => do
    let m ← mkFreshExprSyntheticOpaqueMVar newGoal.toExpr
    goals.modify (m.mvarId! :: ·)
    return m)
  replaceMainGoal (← goals.get)

example {σs : List Type} (Q : SPred σs) (H : Q ⊢ₛ Q) : Q ⊢ₛ Q := by
  mstart
  mintro HQ
  mstop
  exact H

elab_rules : tactic
  | `(tactic| mintro ∀$ident:binderIdent) => do

  let (mvar, goal) ← mStart (← getMainGoal)
  mvar.withContext do

  let goals ← IO.mkRef []
  mvar.assign (← mIntroForall goal ident fun newGoal => do
    let m ← mkFreshExprSyntheticOpaqueMVar newGoal.toExpr
    goals.modify (m.mvarId! :: ·)
    return m)
  replaceMainGoal (← goals.get)

example {σ : Type} {σs : List Type} (Q : SPred (σ::σs)) (H : ∀ s, Q s ⊢ₛ Q s) : Q ⊢ₛ Q := by
  mstart
  mintro H ∀s
  mstop
  exact H s
