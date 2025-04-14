import Lean
import MPL.ProofMode.SGoal

open Lean Elab.Tactic Meta

namespace MPL.ProofMode.Tactics

def sstart (mvar : MVarId) : MetaM (MVarId × SGoal) := mvar.withContext do
  -- check if already in proof mode
  let goal ← instantiateMVars <| ← mvar.getType
  if let some sGoal := parseSGoal? goal then
    return (mvar, sGoal)

  let prop := mkSort .zero
  unless ← isProp goal do
    throwError "type mismatch\n{← mkHasTypeButIsExpectedMsg (← inferType goal) prop}"

  let listType := mkApp (mkConst ``List [.succ .zero]) (mkSort (.succ .zero))
  let σs ← mkFreshExprMVar listType
  let P ← mkFreshExprMVar (mkApp (mkConst ``SPred) σs)
  let inst ← synthInstance (mkApp3 (mkConst ``PropAsEntails) goal σs P)
  let prf := mkApp4 (mkConst ``ProofMode.start_entails) σs P goal inst

  let goal : SGoal := { σs,  hyps := emptyHyp σs, target := P }
  let subgoal /- : Quoted q(⊢ₛ $P)-/ ←
    mkFreshExprSyntheticOpaqueMVar goal.toExpr (← mvar.getTag)
  mvar.assign (mkApp prf subgoal)
  let goal := { goal with target := ← instantiateMVars goal.target }
  pure (subgoal.mvarId!, goal)

elab "sstart" : tactic => do
  let (mvar, _) ← sstart (← getMainGoal)
  replaceMainGoal [mvar]

elab "sstop" : tactic => do
  -- parse goal
  let mvar ← getMainGoal
  mvar.withContext do
  let goal ← instantiateMVars <| ← mvar.getType

  -- check if already in proof mode
  let some sGoal := parseSGoal? goal | throwError "not in proof mode"
  mvar.setType sGoal.strip

example (P Q : SPred [Nat, Bool]) : P ⊢ₛ Q := by
  sstart
  sstop
  admit

/-
-- theorem assumption [BI PROP] {p : Bool} {P P' A Q : PROP} [inst : FromAssumption p A Q]
--   [TCOr (Affine P') (Absorbing Q)] (h : P ⊣⊢ P' ∗ □?p A) : P ⊢ Q :=
--   h.1.trans <| (sep_mono_r inst.1).trans sep_elim_r

--def getFreshName : TSyntax ``binderIdent → CoreM (Name × Syntax)
--  | `(binderIdent| $name:ident) => pure (name.getId, name)
--  | stx => return (← mkFreshUserName `x, stx)

def selectHyp (ty : Expr) : Hyps → MetaM Hyp
  | .strue _ => failure
  | .hyp h => do
    let .true ← isDefEq ty h.p | failure
    pure h
  | .and _ lhs rhs => selectHyp ty rhs <|> selectHyp ty lhs
-/
