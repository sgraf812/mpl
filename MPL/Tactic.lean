import Lean
import MPL.Triple
import MPL.SpecAttr

import MPL.Specs
import MPL.WPMonad
import MPL.WPMonadLift
import Mathlib

namespace MPL

open Lean Meta Elab Tactic

--theorem xwp_lemma {m : Type → Type} [WP m ps] {α} {x : m α} {P : PreCond ps} {Q : PostCond α ps} :
--  P ≤ wp⟦x⟧.apply Q → ⦃P⦄ x ⦃Q⦄ := id

theorem wp_apply_triple {m : Type → Type} {ps : PredShape} [WP m ps] {α} {x : m α} {P : PreCond ps} {Q : PostCond α ps}
  (h : ⦃P⦄ wp x ⦃Q⦄) :
  wp x ≤ PredTrans.prePost P Q := PredTrans.le_prePost (wp_mono x) h

theorem rw_wp {m : Type → Type} {ps : PredShape} [WP m ps] {α} {x : m α} {t : PredTrans ps α}
  (h : wp x = t): wp x ≤ t := h ▸ le_rfl

syntax "xwp" notFollowedBy("|") (ppSpace colGt term:max)* : tactic

macro_rules
  | `(tactic| xwp) => `(tactic| (refine xwp_lemma ?_; try (simp +contextual))) -- contextual needed in test_3 below. TODO: try with grind
  | `(tactic| xwp $x $xs*) => `(tactic| (refine xwp_lemma ?_; try (simp +contextual); intro $x $xs*))

syntax "xapp" (ppSpace colGt term:max)? : tactic

def focus_on_wp (target : Expr) (goal : MVarId) : TacticM Unit := withMainContext do
  match_expr target with
  | LE.le α _ l r =>
    let g::gs ← liftMetaM <| goal.apply (mkConst ``le_trans) | failure
    pushGoals gs
  | _ => throwError "focus_on_wp: unsupported term"

partial def xapp (target : Expr) (spec : Option (TSyntax `term)) : TacticM Unit := withMainContext do
  let_expr triple ps α x P Q := target | throwError "xapp: Not a triple {target}"
  let rec loop (x : Expr) (goal : MVarId) : TacticM Unit := do
    match_expr x with -- `x` is a `PredTrans α`; we want to focus until it is of the form `wp x`
    | WP.wp m ps instWP α x =>
--      let P ← liftMetaM <| mkFreshExprMVar (mkApp (mkConst ``PreCond) ps)
--      let Q ← liftMetaM <| mkFreshExprMVar (mkApp2 (mkConst ``PostCond) α ps)
--      let triple_ty ← mkAppM ``triple #[x, P, Q]
--      let spec_hole ← liftMetaM <| mkFreshExprMVar triple_ty (userName := `spec)
--      dbg_trace s!"triple_ty: {triple_ty}"
--      dbg_trace s!"spec_hole: {spec_hole}"
--      dbg_trace s!"spec_hole type: {← inferType spec_hole}"
--      let wp_apply_triple_app ← mkAppM ``wp_apply_triple #[spec_hole]
      let g::gs ← liftMetaM <| goal.apply (mkApp2 (mkConst ``wp_apply_triple) m ps) | failure
      pushGoals gs
      if let some spec := spec then
--        dbg_trace s!"spec: {spec}"
        let spec ← elabTerm spec none (mayPostpone := true)
--        dbg_trace s!"spec: {spec}"
        let gs ← g.apply spec
        let _ ← instantiateMVars spec
        pushGoals gs
        pruneSolvedGoals
      else
        if x.getAppFn'.isConst then
          let specs ← specAttr.find? x
          if specs.isEmpty then
            throwError s!"no specs found for {x}"
          if specs.size > 1 then
            throwError s!"multiple specs found for {x}: {specs}"
          else
            let gs ← liftMetaM <| g.apply (mkConst specs[0]!)
            pushGoals gs
            pruneSolvedGoals
        else
          throwError s!"not an application of a constant: {x}"
        -- `spec` might have type `wp x = t`. Try `rw_wp`
  --      let y ← liftMetaM <| mkFreshExprMVar (← inferType x) (userName := `y)
  --      let .forallE _ h_ty _ _ ← inferType (mkApp6 (mkConst ``PredTrans.bind_mono) ps α β x y f) | failure
  --      let_expr LE.le _α _inst a b  := h_ty | throwError "xapp: wrong type {h_ty}"
  --      let eq_ty ← mkAppM ``Eq #[a, b]
  --      let spec ← elabTerm spec eq_ty
  --      let gs ← liftMetaM <| h_mvar.apply (← mkAppM ``rw_wp #[spec])
        -- replaceMainGoal (← liftMetaM <| goal.apply (← mkAppM ``rw_wp #[spec]))
    | Bind.bind m _instBind α β x f =>
      let_expr PredTrans ps := m | throwError "xapp: wrong monad {m}"
--      let y ← liftMetaM <| mkFreshExprMVar (← inferType x) (userName := `y)
--      let .forallE _ h_ty _ _ ← inferType (mkApp6 (mkConst ``PredTrans.bind_mono) ps α β x y f) | failure
--      let h ← liftMetaM <| mkFreshExprMVar h_ty (userName := `h)
      let g::gs ← liftMetaM <| goal.apply (mkApp (mkConst ``triple_bind) ps) | failure
      -- now solve `g`, which is `h : x ≤ y`
      pushGoals gs
      loop x g
    | _ => throwError "xapp: unsupported term {target.getArg! 2}"
  loop x (← getMainGoal)

elab "xapp" spec:term : tactic => withMainContext do
  let tgt ← getMainTarget
  xapp tgt spec

theorem test_ex :
  ⦃fun s => s = 4⦄
  wp⟦do
        let mut x := 0
        let s ← get
        for i in [1:s] do { x := x + i; if x > 4 then throw 42 }
        (set 1 : ExceptT Nat (StateT Nat Idd) PUnit)
        return x⟧
  ⦃(fun r s => False,
    fun e s => e = 42 ∧ s = 4,
    ())⦄ := by
  simp
  conv => arg 1; rw[PredTrans.bind_apply]
  simp only [PredTrans.bind_apply]
  apply triple_bind2 (ps:= .except Nat (.arg Nat .pure))
  rw[PredTrans.bind]
--  apply PredTrans.bind_mono (ps := .except Nat (.arg Nat .pure))
--  apply wp_apply_triple
--  apply Specs.forIn_list
  apply triple_bind2 (ps:= .except Nat (.arg Nat .pure))
  xapp (Specs.forIn_list (fun (xs, r) s => r ≤ 4 ∧ s = 4 ∧ r + xs.sum > 4, fun e s => e = 42 ∧ s = 4, ()) ?step)
  case step =>
    intro hd tl x
    xwp s hinv
    split
    · simp[hinv]
    · simp only [PredTrans.pure_apply]; omega
  dsimp
  constructor
  · subst hs; conv in (List.sum _) => { whnf }; simp
  · simp; intro _ _ h; omega

theorem test_ex_2 :
  ⦃fun s => s = 4⦄
  wp⟦do
        let mut x := 0
        let s ← get
        for i in [1:s] do { x := x + i; if x > 4 then set 42 }
        (set 1 : StateT Nat Idd PUnit)
        return x⟧
  ⦃(fun r s => r = 42 ∧ s = 4,
    ())⦄ := by
  simp
  apply intro_state_triple _ _ _; intro s
  dsimp
  apply triple_extract_persistent_true; intro h
  dsimp
  intro s


end MPL
