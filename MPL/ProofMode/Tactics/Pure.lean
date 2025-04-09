/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro
-/
import MPL.ProofMode.SGoal
import MPL.ProofMode.Focus

namespace MPL.ProofMode

open Lean Elab Tactic Meta

class IsPure {σs : List Type} (P : SProp σs) (φ : outParam Prop) where to_pure : P ⊣⊢ₛ ⌜φ⌝
instance (σs) : IsPure (σs:=σs) ⌜φ⌝ φ where to_pure := .rfl
instance (σs) : IsPure (σs:=σs) sprop(⌜φ⌝ → ⌜ψ⌝) (φ → ψ) where to_pure := pure_imp
instance (σs) : IsPure (σs:=σs) sprop(⌜φ⌝ ∧ ⌜ψ⌝) (φ ∧ ψ) where to_pure := pure_and
instance (σs) : IsPure (σs:=σs) sprop(⌜φ⌝ ∨ ⌜ψ⌝) (φ ∨ ψ) where to_pure := pure_or
instance (σs) (P : α → Prop) : IsPure (σs:=σs) sprop(∃ x, ⌜P x⌝) (∃ x, P x) where to_pure := pure_exists
instance (σs) (P : α → Prop) : IsPure (σs:=σs) sprop(∀ x, ⌜P x⌝) (∀ x, P x) where to_pure := pure_forall

theorem spure_thm {σs : List Type} {P P' Q : SProp σs} {φ : Prop} [IsPure Q φ]
  (hfoc : P ⊣⊢ₛ P' ∧ Q) (h : φ → P' ⊢ₛ Q) : P ⊢ₛ Q := by
    have h' : P ⊣⊢ₛ P' ∧ ⌜φ⌝ := hfoc.trans (SProp.and_congr_r IsPure.to_pure)
    have : P' ∧ ⌜φ⌝ ⊢ₛ Q := SProp.and_comm.mp.trans h
  exact hfoc

/-
theorem pure_elim_spatial [BI PROP] {P P' A Q : PROP} {φ : Prop}
    [hA : IntoPure A φ] [or : TCOr (Affine A) (Absorbing Q)]
    (h : P ⊣⊢ P' ∗ A) (h_entails : φ → P' ⊢ Q) : P ⊢ Q :=
  h.1.trans <| match or with
  | TCOr.l =>
    (sep_mono_r <| (affine_affinely A).2.trans (affinely_mono hA.1)).trans <|
    persistent_and_affinely_sep_r.2.trans (pure_elim_r h_entails)
  | TCOr.r =>
    (sep_mono_r <| hA.1.trans absorbingly_affinely_intro_of_persistent).trans <|
    absorbingly_sep_lr.2.trans <| persistent_and_affinely_sep_r.2.trans <|
    pure_elim_r fun hφ => (absorbingly_mono <| h_entails hφ).trans absorbing

theorem pure_elim_intuitionistic [BI PROP] {P P' A Q : PROP} {φ : Prop}
    [IntoPure A φ] (h : P ⊣⊢ P' ∗ □ A) (h' : φ → P' ⊢ Q) : P ⊢ Q :=
  pure_elim_spatial h h'
-/
def ipureCore
    (P P' A Q : Q($prop)) (name : TSyntax ``binderIdent) (pf : Q($P ⊣⊢ $P' ∗ $A))
    (k : (φ : Q(Prop)) → Q($φ) → MetaM (α × Q($P' ⊢ $Q))) : MetaM (α × Q($P ⊢ $Q)) := do
  let φ : Q(Prop) ← mkFreshExprMVarQ q(Prop)
  let inst ← if A.isAppOfArity ``intuitionistically 3 then
    have A' : Q($prop) := A.appArg!
    synthInstance q(IntoPure $A' $φ)
  else
    synthInstance q(IntoPure $A $φ)

  let (name, ref) ← getFreshName name
  withLocalDeclDQ name φ fun p => do
    addLocalVarInfo ref (← getLCtx) p φ
    let (a, m) ← k φ p
    let f : Q($φ → $P' ⊢ $Q) ← mkLambdaFVars #[p] m

    if A.isAppOfArity ``intuitionistically 3 then
      have A' : Q($prop) := A.appArg!
      have : $A =Q iprop(□ $A') := ⟨⟩
      have : Q(IntoPure $A' $φ) := inst
      pure (a, q(pure_elim_intuitionistic $pf $f))
    else
      let _ ← synthInstanceQ q(TCOr (Affine $A) (Absorbing $Q))
      have : Q(IntoPure $A $φ) := inst
      pure (a, q(pure_elim_spatial $pf $f))

def spureCore (res : FocusResult) (k : SGoal → Expr → MetaM α) : MetaM α := do
  let φ ← mkFreshExprMVar (mkSort .zero)
  let inst ← synthInstance (mkApp3 (mkConst ``IsPure) res.restGoal.σs res.focusHyp φ)
  return _

elab "spure" colGt hyp:ident : tactic => do
  let mvar ← getMainGoal
  mvar.withContext do
  let g ← instantiateMVars <| ← mvar.getType
  let some goal := parseSGoal? g | throwError "not in proof mode"

  let some res := goal.focusHyp hyp.getId | throwError "unknown identifier '{hyp}'"

  let (m, pf) ← ipureCore res (← `(binderIdent| $hyp:ident))
  let m ← mkFreshExprSyntheticOpaqueMVar <| SGoal.toExpr res.restGoal
  pure (m, m)

  mvar.assign pf
  replaceMainGoal [m.mvarId!]

elab "iemp_intro" : tactic => do
  let (mvar, { prop, e, goal, .. }) ← istart (← getMainGoal)
  mvar.withContext do

  let .true ← isDefEq goal q(emp : $prop) | throwError "goal is not `emp`"
  let _ ← synthInstanceQ q(Affine $e)
  mvar.assign q(affine (P := $e))
  replaceMainGoal []

theorem pure_intro_affine [BI PROP] {Q : PROP} {φ : Prop}
    [h : FromPure true Q φ] [Affine P] (hφ : φ) : P ⊢ Q :=
  (affine.trans (eq_true hφ ▸ affinely_true.2)).trans h.1

theorem pure_intro_spatial [BI PROP] {Q : PROP} {φ : Prop}
    [h : FromPure false Q φ] (hφ : φ) : P ⊢ Q :=
  (pure_intro hφ).trans h.1

elab "ipure_intro" : tactic => do
  let (mvar, { e, goal, .. }) ← istart (← getMainGoal)
  mvar.withContext do

  let b : Q(Bool) ← mkFreshExprMVarQ q(Bool)
  let φ : Q(Prop) ← mkFreshExprMVarQ q(Prop)
  let _ ← synthInstanceQ q(FromPure $b $goal $φ)
  let m : Q($φ) ← mkFreshExprMVar (← instantiateMVars φ)

  match ← whnf b with
  | .const ``true _ =>
    have : $b =Q true := ⟨⟩
    let _ ← synthInstanceQ q(Affine $e)
    mvar.assign q(pure_intro_affine (P := $e) (Q := $goal) $m)
  | .const ``false _ =>
    have : $b =Q false := ⟨⟩
    mvar.assign q(pure_intro_spatial (P := $e) (Q := $goal) $m)
  | _ => throwError "failed to prove `FromPure _ {goal} _`"
  replaceMainGoal [m.mvarId!]
