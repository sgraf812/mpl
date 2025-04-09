import MPL.ProofMode.SGoal
import Lean.Elab

namespace MPL.ProofMode
open Lean Elab.Tactic Meta

/-- The result of focussing a goal `goal : SGoal` on a particular hypothesis.
The focussed hypothesis is returned as `focusHyp : Expr`, along with the
updated `restGoal : SGoal` and a `proof : Expr` for the property
`goal.hyps ⊣⊢ₛ restGoal.hyps ∧ focusHyp`. -/
structure FocusResult where
  focusHyp : Expr
  restGoal : SGoal
  proof : Expr

theorem focus_l {σs : List Type} {P P' Q R : SProp σs} (h : P ⊣⊢ₛ P' ∧ R) :
    P ∧ Q ⊣⊢ₛ (P' ∧ Q) ∧ R :=
  (SProp.and_congr_l h).trans SProp.and_right_comm

theorem focus_r {σs : List Type} {P Q Q' R : SProp σs} (h : Q ⊣⊢ₛ Q' ∧ R) :
    P ∧ Q ⊣⊢ₛ (P ∧ Q') ∧ R :=
  (SProp.and_congr_r h).trans SProp.and_assoc.symm

partial def SGoal.focusHyp (goal : SGoal) (name : Name) : Option FocusResult :=
  (fun ⟨focused, restHyps, proof⟩ => ⟨focused, { goal with hyps := restHyps }, proof⟩)
  <$> go goal.hyps
  where
    go (e : Expr) : Option (Expr × Expr × Expr) := do
      if let some hyp := parseHyp? e then
        if hyp.name = name then
          return (hyp.p, emptyHyp goal.σs, mkApp2 (mkConst ``SProp.bientails_true_and) goal.σs hyp.p)
        else
          none
      else if let some (σs, lhs, rhs) := parseAnd? e then
        try
          let (rem, lhs', pf) ← go lhs
          return (rem, mkAnd σs lhs' rhs, mkApp6 (mkConst ``focus_l) goal.σs lhs lhs' rhs rem pf)
        catch _ =>
          let (rem, rhs', pf) ← go rhs
          return (rem, mkAnd σs lhs rhs', mkApp6 (mkConst ``focus_r) goal.σs lhs rhs rhs' rem pf)
      else if let some _ := parseEmptyHyp? e then
        none
      else
        panic! s!"SGoal.focusHyp: hypothesis without proper metadata: {e}"
