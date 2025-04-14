/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro
-/
import MPL.ProofMode.SGoal
import MPL.ProofMode.Focus

namespace MPL.ProofMode.Tactics

open Lean Elab Tactic Meta

class IsPure {σs : List Type} (P : SProp σs) (φ : outParam Prop) where to_pure : P ⊣⊢ₛ ⌜φ⌝
instance (σs) : IsPure (σs:=σs) ⌜φ⌝ φ where to_pure := .rfl
instance (σs) : IsPure (σs:=σs) sprop(⌜φ⌝ → ⌜ψ⌝) (φ → ψ) where to_pure := SProp.pure_imp
instance (σs) : IsPure (σs:=σs) sprop(⌜φ⌝ ∧ ⌜ψ⌝) (φ ∧ ψ) where to_pure := SProp.pure_and
instance (σs) : IsPure (σs:=σs) sprop(⌜φ⌝ ∨ ⌜ψ⌝) (φ ∨ ψ) where to_pure := SProp.pure_or
instance (σs) (P : α → Prop) : IsPure (σs:=σs) sprop(∃ x, ⌜P x⌝) (∃ x, P x) where to_pure := SProp.pure_exists
instance (σs) (P : α → Prop) : IsPure (σs:=σs) sprop(∀ x, ⌜P x⌝) (∀ x, P x) where to_pure := SProp.pure_forall

theorem spure_thm {σs : List Type} {P Q T : SProp σs} {φ : Prop} [IsPure Q φ]
  (h : φ → P ⊢ₛ T) : P ∧ Q ⊢ₛ T := by
    apply SProp.pure_elim
    · exact SProp.and_elim_r.trans IsPure.to_pure.mp
    · intro hp
      exact SProp.and_elim_l.trans (h hp)

-- NB: We do not use MVarId.intro because that would mean we require all callers to supply an MVarId.
-- This function only knows about the hypothesis H=⌜φ⌝ to destruct.
-- It will provide a proof for Q ∧ H ⊢ₛ T
-- if `k` produces a proof for Q ⊢ₛ T that may range over a pure proof h : φ.
-- It calls `k` with the φ in H = ⌜φ⌝ and a proof `h : φ` thereof.
def sPureCore (σs : Expr) (hyp : Expr) (name : TSyntax ``binderIdent)
  (k : Expr /-φ:Prop-/ → Expr /-h:φ-/ → MetaM (α × SGoal × Expr)) : MetaM (α × Expr) := do
  let φ ← mkFreshExprMVar (mkSort .zero)
  let inst ← synthInstance (mkApp3 (mkConst ``IsPure) σs hyp φ)
  let (name, ref) ← getFreshHypName name
  withLocalDeclD name φ fun h => do
    -- addLocalVarInfo ref (← getLCtx) h φ
    let (a, goal, prf /- : goal.toExpr -/) ← k φ h
    check prf
    let prf ← mkLambdaFVars #[h] prf
    let prf := mkApp7 (mkConst ``spure_thm) σs goal.hyps hyp goal.target φ inst prf
    check prf
    return (a, prf)

elab "spure" colGt hyp:ident : tactic => do
  let mvar ← getMainGoal
  mvar.withContext do
  let g ← instantiateMVars <| ← mvar.getType
  let some goal := parseSGoal? g | throwError "not in proof mode"
  let some res := goal.focusHyp hyp.getId | throwError "unknown identifier '{hyp}'"
  let (m, prf) ← sPureCore goal.σs res.focusHyp (← `(binderIdent| $hyp:ident)) fun _ _ => do
    let goal := res.restGoal goal
    let m ← mkFreshExprSyntheticOpaqueMVar goal.toExpr
    return (m, goal, m)
  let prf := res.rewriteHyps goal prf
  -- check prf
  mvar.assign prf
  replaceMainGoal [m.mvarId!]

/-- A generalization of `SProp.pure_intro` exploiting `IsPure`. -/
private theorem pure_intro {σs : List Type} {P Q : SProp σs} {φ : Prop} [IsPure Q φ] (hp : φ) : P ⊢ₛ Q :=
  (SProp.pure_intro hp).trans IsPure.to_pure.mpr

macro "spure_intro" : tactic => `(tactic| apply pure_intro)
