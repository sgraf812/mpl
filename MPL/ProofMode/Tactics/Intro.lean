import MPL.ProofMode.Tactics.Basic
import MPL.ProofMode.Patterns.MCases

open Lean Elab Tactic Meta

namespace MPL.ProofMode.Tactics

theorem Intro.intro {σs : List Type} {P Q H T : SPred σs} (hand : Q ∧ H ⊣⊢ₛ P) (h : P ⊢ₛ T) : Q ⊢ₛ H → T :=
  SPred.imp_intro (hand.mp.trans h)

partial def mIntroStep (goal : MGoal) (ident : TSyntax ``binderIdent) (k : MGoal → MetaM Expr) : MetaM Expr := do
  let mkApp3 (.const ``SPred.imp []) σs H T := goal.target | throwError "Target not an implication {goal.target}"
  let (name, _ref) ← getFreshHypName ident
  let Q := goal.hyps
  let H := (Hyp.mk name H).toExpr
  let (P, hand) := mkAnd goal.σs goal.hyps H
  let prf ← k { goal with hyps := P, target := T }
  let prf := mkApp7 (mkConst ``Intro.intro) σs P Q H T hand prf
  return prf

syntax (name := mintro) "mintro" (colGt mcasesPat)+ : tactic
syntax (name := mcases) "mcases" colGt ident "with" colGt mcasesPat : tactic

macro_rules
  | `(tactic| mintro $pat₁ $pat₂ $pats:mcasesPat*) => `(tactic| mintro $pat₁; mintro $pat₂ $pats*)
  | `(tactic| mintro $pat:mcasesPat) => do
    match pat with
    | `(mcasesPat| $_:binderIdent) => Macro.throwUnsupported -- handled by the elaborator below
    | _ => `(tactic| mintro h; mcases h with $pat)

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
