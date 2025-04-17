import MPL.ProofMode.Focus
import MPL.ProofMode.Tactics.Basic

open Lean Elab Tactic Meta

namespace MPL.ProofMode.Tactics

theorem Revert.revert {σs : List Type} {P Q H T : SPred σs} (hfoc : P ⊣⊢ₛ Q ∧ H) (h : Q ⊢ₛ H → T) : P ⊢ₛ T :=
  hfoc.mp.trans (SPred.imp_elim h)

partial def mRevertStep (goal : MGoal) (ref : TSyntax `ident) (k : MGoal → MetaM Expr) : MetaM Expr := do
  let name := ref.getId
  let some res := goal.focusHyp name | throwError "unknown hypothesis '{ref}'"
  let P := goal.hyps
  let Q := res.restHyps
  let H := res.focusHyp
  let T := goal.target
  let prf ← k { goal with hyps := Q, target := mkApp3 (mkConst ``SPred.imp) goal.σs H T }
  let prf := mkApp7 (mkConst ``Revert.revert) goal.σs P Q H T res.proof prf
  return prf

syntax (name := mrevert) "mrevert" colGt ident : tactic

elab "mrevert" colGt h:ident : tactic => do
  let (mvar, goal) ← mStart (← getMainGoal)
  mvar.withContext do

  let goals ← IO.mkRef []
  mvar.assign (← mRevertStep goal h fun newGoal => do
    let m ← mkFreshExprSyntheticOpaqueMVar newGoal.toExpr
    goals.modify (m.mvarId! :: ·)
    return m)
  replaceMainGoal (← goals.get)
