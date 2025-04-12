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

-- goal is P ⊢ₛ T
-- The caller focuses on hypothesis H, P ⊣⊢ₛ Q ∧ H.
-- scasesCore on H and k builds H ⊢ₛ H', then calls k with H'
-- k knows context Q and builds goal P' ⊢ₛ T, a proof of the goal, and a FocusResult for P' ⊣⊢ₛ Q ∧ H'.
-- (k should not also apply H ⊢ₛ H' or unfocus because that does not work with spureCore which needs the see `P'` and not `Q ∧ _`.)
-- then scasesCore builds a proof for Q ∧ H ⊢ₛ T from P' ⊢ₛ T:
--   Q ∧ H ⊢ₐ Q ∧ H' ⊢ₛ P' ⊢ₛ T
-- and finally the caller builds the proof for
--   P ⊢ₛ Q ∧ H ⊢ₛ T
-- by unfocussing.
partial def sCasesCore (σs : Expr) (H : Expr) (pat : SCasesPat) (k : Expr → MetaM (SGoal × Expr × FocusResult)): MetaM Expr := do
  match pat with
  | .one name => do
    let (name, _ref) ← getFreshHypName name
    let H' := (Hyp.mk name H.consumeMData).toExpr
    -- H = H', P = P'
    let (goal, prf, res) ← k H'
    -- res.proof : P' ⊣⊢ₛ Q ∧ H'
    -- goal := P' ⊢ₛ T
    -- prf : goal
    -- Then Q ∧ H ⊢ₛ P' ⊢ₛ T by res.proof.mpr.trans prf
    return (mkApp7 (mkConst ``one) σs goal.hyps res.restHyps res.focusHyp goal.target res.proof prf)
  | .clear => do
    let H' := emptyHyp σs -- H' = ⌜True⌝
    let (goal, prf, res) ← k H'
    -- res.proof : P' ⊣⊢ₛ Q ∧ ⌜True⌝
    -- goal := P' ⊢ₛ T
    -- prf : goal
    -- Then Q ∧ H ⊢ₛ Q ∧ ⌜True⌝ ⊢ₛ P' ⊢ₛ T
    return (mkApp7 (mkConst ``clear) σs goal.hyps res.restHyps H goal.target res.proof prf)
  | .pure arg => do
    let .one n := arg
      | throwError "cannot further destruct a hypothesis after moving it to the Lean context"
    let (_, prf) ← spureCore σs H n fun _ _hφ => do
      let H' := emptyHyp σs
      let (goal, prf, _res) ← k H'
      -- res.proof : P' ⊣⊢ₛ Q ∧ ⌜True⌝
      -- goal := P' ⊢ₛ T
      -- prf : goal (and _hφ may occur freely in the proof)
      -- It is important not to modify goal or prf here, because goal and
      -- prf is what spureCore needs to see.
      return ((), goal, prf)
    -- check prf
    -- Now prf : Q ∧ H ⊢ₛ T (where H is ⌜φ⌝). Exactly what is needed.
    return prf
  | _ => panic! "not implemented"

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
  let prf ← sCasesCore goal.σs H pat fun H' => do
    let (P', hand) := mkAnd goal.σs Q H'
    -- hand : Q ∧ H' ⊣⊢ₛ P'
    -- Need to produce a proof that P' ⊢ₛ T and return res
    let res : FocusResult := { restHyps := Q, focusHyp := H', proof := mkApp4 (mkConst ``SProp.bientails.symm) goal.σs (mkAnd! goal.σs Q H') P' hand }
    let goal := { goal with hyps := P' }
    let m ← mkFreshExprSyntheticOpaqueMVar goal.toExpr
    goals.modify (·.push m.mvarId!)
    return (goal, m, res)
  -- Now prf : Q ∧ H ⊢ₛ T. Prepend hfocus.mp, done.
  let prf := focus.rewriteHyps goal prf
  -- check prf
  mvar.assign prf
  replaceMainGoal (← goals.get).toList
