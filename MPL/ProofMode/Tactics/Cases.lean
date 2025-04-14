import MPL.ProofMode.Focus
import MPL.ProofMode.SCasesPattern
import MPL.ProofMode.Tactics.Basic
import MPL.ProofMode.Tactics.Pure

namespace MPL.ProofMode.Tactics
open Lean Elab Tactic Meta

private theorem one {σs} {P Q H T : SProp σs} (hfocus : P ⊣⊢ₛ Q ∧ H) (hgoal : P ⊢ₛ T) : Q ∧ H ⊢ₛ T :=
  hfocus.mpr.trans hgoal

private theorem clear {σs} {P Q H T : SProp σs} (hfocus : P ⊣⊢ₛ Q ∧ ⌜True⌝) (hgoal : P ⊢ₛ T) : Q ∧ H ⊢ₛ T :=
  (SProp.and_mono_r SProp.true_intro).trans (hfocus.mpr.trans hgoal)

private theorem pure {σs} {P Q T : SProp σs} (hfocus : P ⊣⊢ₛ Q ∧ ⌜True⌝) (hgoal : P ⊢ₛ T) : Q ⊢ₛ T :=
  (SProp.and_intro .rfl SProp.true_intro).trans (hfocus.mpr.trans hgoal)

private theorem refocus_and_2 {σs} {P Q H₁' H₂' H₁₂' : SProp σs} (hfocus : P ⊣⊢ₛ Q ∧ H₁₂') (hand : H₁' ∧ H₂' ⊣⊢ₛ H₁₂') : P ⊣⊢ₛ (Q ∧ H₁') ∧ H₂' :=
  (hfocus.trans (SProp.and_congr_r hand.symm)).trans SProp.and_assoc.symm

private theorem refocus_and_2' {σs} {Q H₁' H₂' H₁₂' : SProp σs} (hand : H₁' ∧ H₂' ⊣⊢ₛ H₁₂') : Q ∧ H₁₂' ⊣⊢ₛ (Q ∧ H₁') ∧ H₂' :=
  (SProp.and_congr_r hand.symm).trans SProp.and_assoc.symm

example (h : a ∧ b) : b := by
  rcases h with ⟨_, hb⟩
  exact hb

-- goal is P ⊢ₛ T
-- The caller focuses on hypothesis H, P ⊣⊢ₛ Q ∧ H.
-- scasesCore on H, pat and k builds H ⊢ₛ H' according to pat, then calls k with H'
-- k knows context Q and builds goal P' ⊢ₛ T, a proof of the goal, and a FocusResult for P' ⊣⊢ₛ Q ∧ H'.
-- (k should not also apply H ⊢ₛ H' or unfocus because that does not work with spureCore which needs the see `P'` and not `Q ∧ _`.)
-- then scasesCore builds a proof for Q ∧ H ⊢ₛ T from P' ⊢ₛ T:
--   Q ∧ H ⊢ₛ Q ∧ H' ⊢ₛ P' ⊢ₛ T
-- and finally the caller builds the proof for
--   P ⊢ₛ Q ∧ H ⊢ₛ T
-- by unfocussing.
partial def sCasesCore (σs : Expr) (H : Expr) (pat : SCasesPat) (k : Expr → MetaM (α × SGoal × Expr × FocusResult)): MetaM (α × SGoal × Expr) := do
  match pat with
  | .one name => do
    let (name, _ref) ← getFreshHypName name
    let H' := (Hyp.mk name H.consumeMData).toExpr
    -- H = H', P = P'
    let (a, goal, prf, res) ← k H'
    -- res.proof : P' ⊣⊢ₛ Q ∧ H'
    -- goal := P' ⊢ₛ T
    -- prf : goal
    -- Then Q ∧ H ⊢ₛ P' ⊢ₛ T by res.proof.mpr.trans prf
    let prf := mkApp7 (mkConst ``one) σs goal.hyps res.restHyps H goal.target res.proof prf
    let goal := { goal with hyps := mkAnd! σs res.restHyps H }
    -- goal.checkProof prf
    return (a, goal, prf)
  | .clear => do
    let H' := emptyHyp σs -- H' = ⌜True⌝
    let (a, goal, prf, res) ← k H'
    -- res.proof : P' ⊣⊢ₛ Q ∧ ⌜True⌝
    -- goal := P' ⊢ₛ T
    -- prf : goal
    -- Then Q ∧ H ⊢ₛ Q ∧ ⌜True⌝ ⊢ₛ P' ⊢ₛ T
    let prf := mkApp7 (mkConst ``clear) σs goal.hyps res.restHyps H goal.target res.proof prf
    let goal := { goal with hyps := mkAnd! σs res.restHyps H }
    return (a, goal, prf)
  | .pure arg => do
    let .one n := arg
      | throwError "cannot further destruct a hypothesis after moving it to the Lean context"
    let (a, goal, prf) ← sPureCore σs H n fun _ _hφ => do
      -- This case is very similar to the clear case, but we need to
      -- return Q ⊢ₛ T, not Q ∧ H ⊢ₛ T.
      let H' := emptyHyp σs -- H' = ⌜True⌝
      let (a, goal, prf, res) ← k H'
      -- res.proof : P' ⊣⊢ₛ Q ∧ ⌜True⌝
      -- goal := P' ⊢ₛ T
      -- prf : goal
      -- Then Q ⊢ₛ Q ∧ ⌜True⌝ ⊢ₛ P' ⊢ₛ T
      let prf := mkApp6 (mkConst ``pure) σs goal.hyps res.restHyps goal.target res.proof prf
      let goal := res.restGoal goal -- Q ⊢ₛ T
      return (a, goal, prf)
    -- Now prf : Q ∧ H ⊢ₛ T (where H is ⌜φ⌝). Exactly what is needed.
    return (a, goal, prf)
  | .conjunction [] => sCasesCore σs H .clear k
  | .conjunction [p] => sCasesCore σs H p k
  --| .conjunction (p :: ps) => do
  --  let some (σs, H₁, H₂) := parseAnd? H | throwError "Not a conjunction {H}"
  --  -- goal is Q ∧ (H₁ ∧ H₂) ⊢ₛ T
  --  -- we can recurse on H₁ to get Q ∧ H₁ ⊢ₛ T.
  --  let prf ← sCasesCore σs H₁ p fun H₁' => do
  --    let prf ← sCasesCore σs H₂ (.conjunction ps) fun H₂' => do
  --      let (H₁₂', hand) := mkAnd σs H₁' H₂'
  --      let (goal, prf, res) ← k H₁₂'
  --      -- goal : P' ⊢ₛ T
  --      -- prf : goal
  --      -- res.proof : P' ⊣⊢ₛ Q ∧ H₁₂'
  --      -- need to refocus to
  --      -- res.proof : P' ⊣⊢ₛ (Q ∧ H₁') ∧ H₂'
  --      let P' := goal.hyps
  --      let Q := res.restHyps
  --      let refocus := mkApp7 (mkConst ``refocus_and_2) σs P' Q H₁₂' H₁' H₂' res.proof hand
  --      let res := { restHyps := mkAnd! σs Q H₁', focusHyp := H₂', proof := refocus }
  --      return (goal, prf, res)
  --    -- prf : (Q ∧ H₁') ∧ H₂ ⊢ₛ T
  --    -- refocus on H₁'

  --  return (mkApp4 (mkConst ``conjunction) σs goal.hyps res.restHyps goal.focusHyp goal.target)
  --  -- Goal is Q ∧ H₁ ⊢ₛ T
  --  return (mkApp4 (mkConst ``conjunction) σs goal.hyps res.restHyps goal.focusHyp goal.target)
  | _ => throwError "not implemented"

private theorem assembled_proof {σs} {P P' Q H H' T : SProp σs}
  (hfocus : P ⊣⊢ₛ Q ∧ H) (hcases : H ⊢ₛ H') (hand : Q ∧ H' ⊣⊢ₛ P') (hprf₃ : P' ⊢ₛ T) : P ⊢ₛ T :=
  hfocus.mp.trans ((SProp.and_mono_r hcases).trans (hand.mp.trans hprf₃))

private theorem blah2 {σs} {P Q H R : SProp σs}
  (h₁ : P ⊣⊢ₛ Q ∧ H) (h₂ : Q ∧ H ⊢ₛ R) : P ⊢ₛ R :=
  h₁.mp.trans h₂

private theorem blah3 {σs} {P Q H T : SProp σs}
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
  let (_, _new_goal, prf) ← sCasesCore goal.σs H pat fun H' => do
    let (P', hand) := mkAnd goal.σs Q H'
    -- hand : Q ∧ H' ⊣⊢ₛ P'
    -- Need to produce a proof that P' ⊢ₛ T and return res
    let res : FocusResult := { restHyps := Q, focusHyp := H', proof := mkApp4 (mkConst ``SProp.bientails.symm) goal.σs (mkAnd! goal.σs Q H') P' hand }
    let goal := { goal with hyps := P' }
    let m ← mkFreshExprSyntheticOpaqueMVar goal.toExpr
    goals.modify (·.push m.mvarId!)
    return ((), goal, m, res)
  _new_goal.checkProof prf
  -- Now prf : Q ∧ H ⊢ₛ T. Prepend hfocus.mp, done.
  let prf := focus.rewriteHyps goal prf
  -- check prf
  mvar.assign prf
  replaceMainGoal (← goals.get).toList
