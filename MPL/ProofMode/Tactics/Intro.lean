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

partial def mIntroStep (goal : MGoal) (ident : TSyntax ``binderIdent) (k : MGoal → MetaM Expr) : MetaM Expr := do
  let some (σs, H, T) := goal.target.app3? ``SPred.imp | throwError "Target not an implication {goal.target}"
  let (name, _ref) ← getFreshHypName ident
  let Q := goal.hyps
  let H := (Hyp.mk name H).toExpr
  let (P, hand) := mkAnd goal.σs goal.hyps H
  let prf ← k { goal with hyps := P, target := T }
  let prf := mkApp7 (mkConst ``Intro.intro) σs P Q H T hand prf
  return prf

private partial def betaRevPreservingHypNames (σs' e : Expr) (args : Array Expr) : Expr :=
  if let some _σs := parseEmptyHyp? e then
    emptyHyp σs'
  else if let some hyp := parseHyp? e then
    { hyp with p := hyp.p.betaRev args }.toExpr
  else if let some (_σs, lhs, rhs) := parseAnd? e then
    -- _σs = σ :: σs'
    mkAnd! σs' (betaRevPreservingHypNames σs' lhs args) (betaRevPreservingHypNames σs' rhs args)
  else
    e.betaRev args

-- This is regular MVar.intro, but it takes care not to leave the proof mode by preserving metadata
partial def mForallIntroStep (goal : MGoal) (ident : TSyntax ``binderIdent) (k : MGoal → MetaM Expr) : MetaM Expr := do
  let some (_type, σ, σs') := (← whnf goal.σs).app3? ``List.cons | throwError "Ambient state list not a cons {goal.σs}"
  let name ← match ident with
  | `(binderIdent| $name:ident) => pure name.getId
  | `(binderIdent| $_) => mkFreshUserName `s
  withLocalDeclD name σ fun s => do
    let H := betaRevPreservingHypNames σs' goal.hyps #[s]
    let T := goal.target.betaRev #[s]
    let prf ← mkLambdaFVars #[s] (← k { σs:=σs', hyps:=H, target:=T })
    return mkApp5 (mkConst ``SPred.entails_cons_intro) σ σs' goal.hyps goal.target prf

syntax (name := mintro) "mintro" (colGt mintroPat)+ : tactic
syntax (name := mcases) "mcases" colGt ident "with" colGt mcasesPat : tactic

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
  mvar.assign (← mIntroStep goal ident fun newGoal => do
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
  mvar.assign (← mForallIntroStep goal ident fun newGoal => do
    let m ← mkFreshExprSyntheticOpaqueMVar newGoal.toExpr
    goals.modify (m.mvarId! :: ·)
    return m)
  replaceMainGoal (← goals.get)

example {σ : Type} {σs : List Type} (Q : SPred (σ::σs)) (H : ∀ s, Q s ⊢ₛ Q s) : Q ⊢ₛ Q := by
  mstart
  mintro H ∀s
  mstop
  exact H s
