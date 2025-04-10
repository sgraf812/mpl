import MPL.ProofMode.SGoal
import Lean.Elab

namespace MPL.ProofMode
open Lean Elab.Tactic Meta

/-- The result of focussing the context of a goal `goal : SGoal` on a particular hypothesis.
The focussed hypothesis is returned as `focusHyp : Expr`, along with the
residual `restHyps : Expr` and a `proof : Expr` for the property
`goal.hyps ⊣⊢ₛ restHyps ∧ focusHyp`. -/
structure FocusResult where
  focusHyp : Expr
  restHyps : Expr
  proof : Expr

def FocusResult.restGoal (res : FocusResult) (goal : SGoal) : SGoal :=
  { goal with hyps := res.restHyps }

theorem focus_this {σs : List Type} {P : SProp σs} : P ⊣⊢ₛ ⌜True⌝ ∧ P :=
  SProp.true_and.symm

theorem focus_l {σs : List Type} {P P' Q C R : SProp σs} (h₁ : P ⊣⊢ₛ P' ∧ R) (h₂ : P' ∧ Q ⊣⊢ₛ C) :
    P ∧ Q ⊣⊢ₛ C ∧ R :=
  (SProp.and_congr_l h₁).trans (SProp.and_right_comm.trans (SProp.and_congr_l h₂))

theorem focus_r {σs : List Type} {P Q Q' C R : SProp σs} (h₁ : Q ⊣⊢ₛ Q' ∧ R) (h₂ : P ∧ Q' ⊣⊢ₛ C) :
    P ∧ Q ⊣⊢ₛ C ∧ R :=
  (SProp.and_congr_r h₁).trans (SProp.and_assoc.symm.trans (SProp.and_congr_l h₂))

partial def focusHyp (σs : Expr) (e : Expr) (name : Name) : Option FocusResult := do
  if let some hyp := parseHyp? e then
    if hyp.name = name then
      return ⟨e, emptyHyp σs, mkApp2 (mkConst ``focus_this) σs e⟩
    else
      none
  else if let some (σs, lhs, rhs) := parseAnd? e then
    try
      let ⟨focus, lhs', h₁⟩ ← focusHyp σs lhs name
      let ⟨C, h₂⟩ := mkAnd σs lhs' rhs
      return ⟨focus, C, mkApp8 (mkConst ``focus_l) σs lhs lhs' rhs C focus h₁ h₂⟩
    catch _ =>
      let ⟨focus, rhs', h₁⟩ ← focusHyp σs rhs name
      let ⟨C, h₂⟩ := mkAnd σs lhs rhs'
      return ⟨focus, C, mkApp8 (mkConst ``focus_r) σs lhs rhs rhs' C focus h₁ h₂⟩
  else if let some _ := parseEmptyHyp? e then
    none
  else
    panic! s!"focusHyp: hypothesis without proper metadata: {e}"

partial def SGoal.focusHyp (goal : SGoal) (name : Name) : Option FocusResult :=
  MPL.ProofMode.focusHyp goal.σs goal.hyps name
