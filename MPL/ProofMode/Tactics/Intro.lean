import MPL.ProofMode.Tactics.Basic
open Lean Elab Tactic Meta

namespace MPL.ProofMode.Tactics

theorem imp_intro_empty {σs : List Type} {P Q : SProp σs} (h : P ⊢ₛ Q) : ⊢ₛ P → Q :=
  (SProp.entails_true_intro P Q).mpr h

def getFreshHypName : TSyntax ``binderIdent → CoreM (Name × Syntax)
  | `(binderIdent| $name:ident) => pure (name.getId, name)
  | stx => return (← mkFreshUserName `h, stx)

partial def sIntroCore
    (goal : SGoal) (proofs : Array Expr) (idents : List (TSyntax ``binderIdent)) :
    MetaM (SGoal × Array Expr) := do
  match idents with
  | [] => pure (goal, proofs)
  | ident :: idents =>
    let mkApp3 (.const ``SProp.imp []) σs p q := goal.target | throwError "Target not an implication {goal.target}"
    let (name, _ref) ← getFreshHypName ident
    let uniq ← mkFreshId
    let hyp : Hyp := { name := name, uniq := uniq, p := p }
    let p := hyp.toExpr
    if let some _ := parseEmptyHyp? goal.hyps then
      let proof := mkApp3 (mkConst ``imp_intro_empty) σs p q
      let newGoal := { goal with hyps := p, target := q }
      sIntroCore newGoal (proofs.push proof) idents
    else
      let proof := mkApp4 (mkConst ``SProp.imp_intro) σs goal.hyps p q
      let newGoal := { goal with hyps := mkAnd σs goal.hyps p, target := q }
      sIntroCore newGoal (proofs.push proof) idents

-- elab "sintro" pats:(colGt icasesPat)* : tactic => do
elab "sintro" idents:(colGt binderIdent)* : tactic => do
  -- parse syntax
--  let pats ← liftMacroM <| pats.mapM <| iCasesPat.parse

  let (mvar, goal) ← sstart (← getMainGoal)
  mvar.withContext do

  -- process patterns
  let (newGoal, proofs) ← sIntroCore goal #[] idents.toList
  let m ← mkFreshExprSyntheticOpaqueMVar <| SGoal.toExpr newGoal
  mvar.assign (proofs.foldr mkApp m)
  replaceMainGoal [m.mvarId!]

example {σs : List Type} (Q : SProp σs) (H : Q ⊢ₛ Q) : Q ⊢ₛ Q := by
  sstart
  sintro HQ
  sstop
  exact H
