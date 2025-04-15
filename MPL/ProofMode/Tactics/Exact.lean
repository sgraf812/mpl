import MPL.ProofMode.Tactics.Basic
import MPL.ProofMode.Focus

namespace MPL.ProofMode.Tactics
open Lean Elab Tactic Meta

theorem Exact.assumption {σs : List Type} {P P' A : SPred σs}
  (h : P ⊣⊢ₛ P' ∧ A) : P ⊢ₛ A := h.mp.trans SPred.and_elim_r

theorem Exact.from_tautology {σs : List Type} {P T : SPred σs} (htaut : ⊢ₛ T) : P ⊢ₛ T :=
  SPred.true_intro.trans htaut

def _root_.MPL.ProofMode.SGoal.exact (goal : SGoal) (hyp : TSyntax `ident) : OptionT MetaM Expr := do
  let some focusRes := goal.focusHyp hyp.raw.getId | failure
  OptionT.mk do
  let proof := mkApp5 (mkConst ``Exact.assumption) goal.σs goal.hyps focusRes.restHyps goal.target focusRes.proof
  unless ← isDefEq focusRes.focusHyp goal.target do
    throwError "sexact tactic failed, hypothesis {hyp} is not definitionally equal to {goal.target}"
  return proof

def _root_.MPL.ProofMode.SGoal.exactPure (goal : SGoal) (hyp : TSyntax `ident) : OptionT MetaM Expr := do
  let some decl := (← getLCtx).findFromUserName? hyp.raw.getId | failure
  OptionT.mk do
  let T := goal.target
  let expected := mkApp2 (mkConst ``SPred.tautological) goal.σs T
  unless ← isDefEq decl.type expected do
    throwError "sexact tactic failed, pure hypothesis {decl.userName} is not definitionally equal to {expected}"
  return mkApp4 (mkConst ``Exact.from_tautology) goal.σs goal.hyps goal.target (mkFVar decl.fvarId)

elab "sexact" colGt hyp:ident : tactic => do
  let mvar ← getMainGoal
  mvar.withContext do
  let g ← instantiateMVars <| ← mvar.getType
  let some goal := parseSGoal? g | throwError "not in proof mode"
  let some proof ← liftMetaM <|
    goal.exact hyp <|> goal.exactPure hyp
    | throwError "hypothesis not found"
  mvar.assign proof
  replaceMainGoal []
