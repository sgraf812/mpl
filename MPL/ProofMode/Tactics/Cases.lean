import MPL.ProofMode.Focus
import MPL.ProofMode.SCasesPattern
import MPL.ProofMode.Tactics.Basic
import MPL.ProofMode.Tactics.Pure

namespace MPL.ProofMode.Tactics
open Lean Elab Tactic Meta

theorem SCases.add_goal {σs} {P Q H T : SPred σs} (hand : Q ∧ H ⊣⊢ₛ P) (hgoal : P ⊢ₛ T) : Q ∧ H ⊢ₛ T :=
  hand.mp.trans hgoal

theorem SCases.clear {σs} {Q H T : SPred σs} (hgoal : Q ∧ ⌜True⌝ ⊢ₛ T) : Q ∧ H ⊢ₛ T :=
  (SPred.and_mono_r SPred.true_intro).trans hgoal

theorem SCases.pure {σs} {Q T : SPred σs} (hgoal : Q ∧ ⌜True⌝ ⊢ₛ T) : Q ⊢ₛ T :=
  (SPred.and_intro .rfl SPred.true_intro).trans hgoal

theorem SCases.and_1 {σs} {Q H₁' H₂' H₁₂' T : SPred σs} (hand : H₁' ∧ H₂' ⊣⊢ₛ H₁₂') (hgoal : Q ∧ H₁₂' ⊢ₛ T) : (Q ∧ H₁') ∧ H₂' ⊢ₛ T :=
  ((SPred.and_congr_r hand.symm).trans SPred.and_assoc.symm).mpr.trans hgoal

theorem SCases.and_2 {σs} {Q H₁' H₂ T : SPred σs} (hgoal : (Q ∧ H₁') ∧ H₂ ⊢ₛ T) : (Q ∧ H₂) ∧ H₁' ⊢ₛ T :=
  SPred.and_right_comm.mp.trans hgoal

theorem SCases.and_3 {σs} {Q H₁ H₂ T : SPred σs} (hgoal : (Q ∧ H₂) ∧ H₁ ⊢ₛ T) : Q ∧ (H₁ ∧ H₂) ⊢ₛ T :=
  SPred.and_assoc.mpr.trans (SPred.and_right_comm.mp.trans hgoal)

example (h : a ∧ b) : b := by
  rcases h with ⟨_, hb⟩
  exact hb

-- Produce a proof for Q ∧ H ⊢ₛ T by opening a new goal P ⊢ₛ T, where P ⊣⊢ₛ Q ∧ H.
def sCasesAddGoal (goals : IO.Ref (Array MVarId)) (σs : Expr) (T : Expr) (Q : Expr) (H : Expr) : MetaM (Unit × SGoal × Expr) := do
  let (P, hand) := mkAnd σs Q H
  -- hand : Q ∧ H ⊣⊢ₛ P
  -- Need to produce a proof that P ⊢ₛ T and return res
  let goal : SGoal := { σs := σs, hyps := P, target := T }
  let m ← mkFreshExprSyntheticOpaqueMVar goal.toExpr
  goals.modify (·.push m.mvarId!)
  let prf := mkApp7 (mkConst ``SCases.add_goal) σs P Q H T hand m
  let goal := { goal with hyps := mkAnd! σs Q H }
  return ((), goal, prf)

private def getQH (goal : SGoal) : MetaM (Expr × Expr) := do
  let some (_, Q, H) := parseAnd? goal.hyps | throwError m!"Internal error: Hypotheses not a conjunction {goal.hyps}"
  return (Q, H)

-- goal is P ⊢ₛ T
-- The caller focuses on hypothesis H, P ⊣⊢ₛ Q ∧ H.
-- scasesCore on H, pat and k builds H ⊢ₛ H' according to pat, then calls k with H'
-- k knows context Q and builds goal Q ∧ H' ⊢ₛ T and a proof of the goal.
-- (k should not also apply H ⊢ₛ H' or unfocus because that does not work with spureCore which needs the see `P'` and not `Q ∧ _`.)
-- then scasesCore builds a proof for Q ∧ H ⊢ₛ T from P' ⊢ₛ T:
--   Q ∧ H ⊢ₛ Q ∧ H' ⊢ₛ P' ⊢ₛ T
-- and finally the caller builds the proof for
--   P ⊢ₛ Q ∧ H ⊢ₛ T
-- by unfocussing.
partial def sCasesCore (σs : Expr) (H : Expr) (pat : SCasesPat) (k : Expr → MetaM (α × SGoal × Expr)): MetaM (α × SGoal × Expr) := do
  match pat with
  | .one name => do
    let (name, _ref) ← getFreshHypName name
    let H' := (Hyp.mk name H.consumeMData).toExpr
    k H'
    -- prf : Q ∧ H' ⊢ₛ T, but H = H' so nothing to do.
  | .clear => do
    let H' := emptyHyp σs -- H' = ⌜True⌝
    let (a, goal, prf) ← k H'
    let (Q, _H) ← getQH goal
    -- prf : Q ∧ ⌜True⌝ ⊢ₛ T
    -- Then Q ∧ H ⊢ₛ Q ∧ ⌜True⌝ ⊢ₛ T
    let prf := mkApp5 (mkConst ``SCases.clear) σs Q H goal.target prf
    let goal := { goal with hyps := mkAnd! σs Q H }
    return (a, goal, prf)
  | .pure arg => do
    let .one n := arg
      | throwError "cannot further destruct a hypothesis after moving it to the Lean context"
    let (a, goal, prf) ← sPureCore σs H n fun _ _hφ => do
      -- This case is very similar to the clear case, but we need to
      -- return Q ⊢ₛ T, not Q ∧ H ⊢ₛ T.
      let H' := emptyHyp σs -- H' = ⌜True⌝
      let (a, goal, prf) ← k H'
      let (Q, _H) ← getQH goal
      -- prf : Q ∧ ⌜True⌝ ⊢ₛ T
      -- Then Q ⊢ₛ Q ∧ ⌜True⌝ ⊢ₛ T
      let prf := mkApp4 (mkConst ``SCases.pure) σs Q goal.target prf
      let goal := { goal with hyps := Q }
      return (a, goal, prf)
    -- Now prf : Q ∧ H ⊢ₛ T (where H is ⌜φ⌝). Exactly what is needed.
    return (a, goal, prf)
  | .persistent arg => sCasesCore σs H arg k
  | .tuple [] => sCasesCore σs H .clear k
  | .tuple [p] => sCasesCore σs H p k
  | .tuple (p :: ps) => do
    let some (σs, H₁, H₂) := parseAnd? H.consumeMData | throwError "Not a conjunction {H}"
    -- goal is Q ∧ (H₁ ∧ H₂) ⊢ₛ T. Plan:
    -- 1. Recurse on H₁ and H₂.
    -- 2. The inner callback sees H₁' and H₂' and calls k on H₁₂', where H₁₂' = mkAnd H₁' H₂'
    -- 3. The inner callback receives P' ⊢ₛ T, where (P' ⊣⊢ₛ Q ∧ H₁₂').
    -- 4. The inner callback returns (Q ∧ H₁') ∧ H₂' ⊢ₛ T
    -- 5. The outer callback receives (Q ∧ H₁') ∧ H₂ ⊢ₛ T
    -- 6. The outer callback reassociates and returns (Q ∧ H₂) ∧ H₁' ⊢ₛ T
    -- 7. The top-level receives (Q ∧ H₂) ∧ H₁ ⊢ₛ T
    -- 8. Reassociate to Q ∧ (H₁ ∧ H₂) ⊢ₛ T and return it.
    let ((a, Q), goal, prf) ← sCasesCore σs H₁ p fun H₁' => do
      let ((a, Q), goal, prf) ← sCasesCore σs H₂ (.tuple ps) fun H₂' => do
        let (H₁₂', hand) := mkAnd σs H₁' H₂'
        let (a, goal, prf) ← k H₁₂' -- (2)
        -- (3) prf : Q ∧ H₁₂' ⊢ₛ T
        -- (4) refocus to (Q ∧ H₁') ∧ H₂'
        let (Q, _H) ← getQH goal
        let T := goal.target
        let prf := mkApp8 (mkConst ``SCases.and_1) σs Q H₁' H₂' H₁₂' T hand prf
        -- check prf
        let QH₁' := mkAnd! σs Q H₁'
        let goal := { goal with hyps := mkAnd! σs QH₁' H₂' }
        return ((a, Q), goal, prf)
      -- (5) prf : (Q ∧ H₁') ∧ H₂ ⊢ₛ T
      -- (6) refocus to prf : (Q ∧ H₂) ∧ H₁' ⊢ₛ T
      let prf := mkApp6 (mkConst ``SCases.and_2) σs Q H₁' H₂ goal.target prf
      let QH₂ := mkAnd! σs Q H₂
      let goal := { goal with hyps := mkAnd! σs QH₂ H₁' }
      return ((a, Q), goal, prf)
    -- (7) prf : (Q ∧ H₂) ∧ H₁ ⊢ₛ T
    -- (8) rearrange to Q ∧ (H₁ ∧ H₂) ⊢ₛ T
    let prf := mkApp6 (mkConst ``SCases.and_3) σs Q H₁ H₂ goal.target prf
    let goal := { goal with hyps := mkAnd! σs Q H }
    return (a, goal, prf)
  | .alts [] => throwUnsupportedSyntax
  | .alts [p] => sCasesCore σs H p k
  | .alts (p :: ps) => do
    let some (σs, H₁, H₂) := H.consumeMData.app3? ``SPred.or | throwError "Not a disjunction {H}"
    -- goal is Q ∧ (H₁ ∨ H₂) ⊢ₛ T. Plan:
    -- 1. Recurse on H₁ and H₂ with the same k.
    -- 2. Receive proofs for Q ∧ H₁ ⊢ₛ T and Q ∧ H₂ ⊢ₛ T.
    -- 3. Build a proof for Q ∧ (H₁ ∨ H₂) ⊢ₛ T from them.
    let (_a, goal₁,  prf₁) ← sCasesCore σs H₁ p k
    let (a,  _goal₂, prf₂) ← sCasesCore σs H₂ (.alts ps) k
    let (Q, _H₁) ← getQH goal₁
    let goal := { goal₁ with hyps := mkAnd! σs Q (mkApp3 (mkConst ``SPred.or) σs H₁ H₂) }
    let prf := mkApp7 (mkConst ``SPred.and_or_elim_r) σs Q H₁ H₂ goal.target prf₁ prf₂
    return (a, goal, prf)

private theorem assembled_proof {σs} {P P' Q H H' T : SPred σs}
  (hfocus : P ⊣⊢ₛ Q ∧ H) (hcases : H ⊢ₛ H') (hand : Q ∧ H' ⊣⊢ₛ P') (hprf₃ : P' ⊢ₛ T) : P ⊢ₛ T :=
  hfocus.mp.trans ((SPred.and_mono_r hcases).trans (hand.mp.trans hprf₃))

private theorem blah2 {σs} {P Q H R : SPred σs}
  (h₁ : P ⊣⊢ₛ Q ∧ H) (h₂ : Q ∧ H ⊢ₛ R) : P ⊢ₛ R :=
  h₁.mp.trans h₂

private theorem blah3 {σs} {P Q H T : SPred σs}
  (hand : Q ∧ H ⊣⊢ₛ P) (hgoal : P ⊢ₛ T) : Q ∧ H ⊢ₛ T :=
  hand.mp.trans hgoal

elab "scases" colGt hyp:ident "with" colGt pat:scasesPat : tactic => do
  let pat ← liftMacroM <| SCasesPat.parse pat
  let (mvar, goal) ← sstart (← getMainGoal)
  mvar.withContext do

  let some focus := goal.focusHyp hyp.getId | throwError "unknown hypothesis '{hyp}'"
  -- goal : P ⊢ₛ T,
  -- hfocus : P ⊣⊢ₛ Q ∧ H
  let Q := focus.restHyps
  let H := focus.focusHyp
  let goals ← IO.mkRef #[]
  let (_, _new_goal, prf) ← sCasesCore goal.σs H pat (sCasesAddGoal goals goal.σs goal.target Q)

  -- Now prf : Q ∧ H ⊢ₛ T. Prepend hfocus.mp, done.
  let prf := focus.rewriteHyps goal prf
  -- check prf
  mvar.assign prf
  replaceMainGoal (← goals.get).toList
