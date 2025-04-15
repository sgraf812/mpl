import MPL.ProofMode.Tactics.Basic
import MPL.ProofMode.SCasesPattern

open Lean Elab Tactic Meta

namespace MPL.ProofMode.Tactics

theorem Intro.intro {σs : List Type} {P Q H T : SPred σs} (hand : Q ∧ H ⊣⊢ₛ P) (h : P ⊢ₛ T) : Q ⊢ₛ H → T :=
  SPred.imp_intro (hand.mp.trans h)

partial def sIntroStep (goal : SGoal) (ident : TSyntax ``binderIdent) (k : SGoal → MetaM Expr) : MetaM Expr := do
  let mkApp3 (.const ``SPred.imp []) σs H T := goal.target | throwError "Target not an implication {goal.target}"
  let (name, _ref) ← getFreshHypName ident
  let Q := goal.hyps
  let H := (Hyp.mk name H).toExpr
  let (P, hand) := mkAnd goal.σs goal.hyps H
  let prf ← k { goal with hyps := P, target := T }
  let prf := mkApp7 (mkConst ``Intro.intro) σs P Q H T hand prf
  return prf

syntax (name := sintro) "sintro" (colGt scasesPat)+ : tactic
syntax (name := scases) "scases" colGt ident "with" colGt scasesPat : tactic

macro_rules
  | `(tactic| sintro $pat₁ $pat₂ $pats:scasesPat*) => `(tactic| sintro $pat₁; sintro $pat₂ $pats*)
  | `(tactic| sintro $pat:scasesPat) => do
    match pat with
    | `(scasesPat| $_:binderIdent) => Macro.throwUnsupported -- handled by the elaborator  e
    | _ => `(tactic| sintro h; scases h with $pat)

elab_rules : tactic
  | `(tactic| sintro $ident:binderIdent) => do

  let (mvar, goal) ← sstart (← getMainGoal)
  mvar.withContext do

  let goals ← IO.mkRef []
  mvar.assign (← sIntroStep goal ident fun newGoal => do
    let m ← mkFreshExprSyntheticOpaqueMVar newGoal.toExpr
    goals.modify (m.mvarId! :: ·)
    return m)
  replaceMainGoal (← goals.get)

example {σs : List Type} (Q : SPred σs) (H : Q ⊢ₛ Q) : Q ⊢ₛ Q := by
  sstart
  sintro HQ
  sstop
  exact H
