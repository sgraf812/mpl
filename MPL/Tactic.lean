import Lean
import MPL.Triple
import MPL.SpecAttr

import MPL.Specs
import MPL.WPMonad
import MPL.WPMonadLift
import MPL.WPSimp
import Mathlib

namespace MPL

open Lean Meta Elab Tactic

theorem xwp_lemma {m : Type → Type} [WP m ps] {α} {x : m α} {P : PreCond ps} {Q : PostCond α ps} :
  {{P}} wp⟦x⟧ {{Q}} → ⦃P⦄ x ⦃Q⦄ := id

theorem wp_apply_triple {m : Type → Type} {ps : PredShape} [WP m ps] {α} {x : m α} {P : PreCond ps} {Q : PostCond α ps}
  (h : ⦃P⦄ x ⦃Q⦄) :
  P ≤ wp⟦x⟧.apply Q := h

theorem wp_apply_triple_conseq {m : Type → Type} {ps : PredShape} [WP m ps] {α} {x : m α} {P : PreCond ps} {Q Q' : PostCond α ps}
  (h : ⦃P⦄ x ⦃Q⦄) (hpost : Q ≤ Q') :
  P ≤ wp⟦x⟧.apply Q' := le_trans h (wp⟦x⟧.mono _ _ hpost)

theorem wp_apply_triple_pointfree {m : Type → Type} {ps : PredShape} [WP m ps] {α} {x : m α} {P : PreCond ps} {Q : PostCond α ps}
  (h : ⦃P⦄ x ⦃Q⦄) :
  wp x ≤ PredTrans.prePost P Q := PredTrans.le_prePost.mp h

theorem rw_wp {m : Type → Type} {ps : PredShape} [WP m ps] {α} {x : m α} {t : PredTrans ps α}
  (h : wp x = t): wp x ≤ t := h ▸ le_rfl

macro "xstart" : tactic => `(tactic| (refine xwp_lemma ?_))

@[simp]
theorem ite_extrude_yield {c : Prop} [Decidable c] {x y : α} :
  (if c then pure (.yield x) else pure (.yield y)) = ForInStep.yield <$> if c then pure x else pure (f := Idd) y := by
  split <;> simp

-- TODO: upstream
@[simp] theorem Array.forIn'_eq_forIn'_toList {α β} [Monad m] (arr : Array α)
    (init : β) (f : (a : α) → a ∈ arr → β → m (ForInStep β)) :
    forIn' arr init f =
      forIn' arr.toList init (fun a h => f a (Array.mem_toList.mp h)) := by
  conv => lhs; simp only [forIn', Array.forIn']
  simp
  sorry -- do the same as for Std.Range
  -- rw [forIn'_loop_eq_forIn'_range']

@[simp] theorem Array.forIn_eq_forIn_toList {α β} [Monad m] (arr : Array α)
    (init : β) (f : α → β → m (ForInStep β)) :
    forIn arr init f = forIn arr.toList init f := by
  simp only [forIn, forIn'_eq_forIn'_toList]

-- not sure how to do this in a non-bloaty way. Probably involves a type class
--@[simp] theorem List.forIn_MProd_to_Prod {α β} [Monad m]
    --(init : β) (f : α → β → m (ForInStep β)) :
    --forIn xs init f = forIn xs init f := by
  --simp only [forIn, forIn'_eq_forIn'_toList]

attribute [wp_simp]
  wp_pure wp_bind wp_map wp_seq wp_ite wp_dite wp_monadLift
  pure_bind bind_assoc bind_pure_comp bind_pure map_pure id_map'
  PredTrans.pure_apply PredTrans.bind_apply PredTrans.map_apply
  -- List.Zipper.begin_suff List.Zipper.tail_suff List.Zipper.end_suff -- Zipper stuff needed for invariants
  Std.Range.forIn_eq_forIn_range' Std.Range.forIn'_eq_forIn'_range' Std.Range.size Nat.div_one  -- rewrite to forIn_list
  Array.forIn_eq_forIn_toList Array.forIn'_eq_forIn'_toList -- rewrite to forIn_list
  ite_extrude_yield List.forIn_yield_eq_foldlM -- rewrite to foldlM
  PredTrans.dropFail PredTrans.drop_fail_cond -- TODO: Can we do this whole lifting business with fewer simp rules?
  MonadState.wp_get MonadStateOf.wp_get StateT.wp_get PredTrans.get
  MonadState.wp_set MonadStateOf.wp_set StateT.wp_set PredTrans.set
  ExceptT.map_throw ExceptT.wp_throw PredTrans.throw

macro "xwp" : tactic =>
  `(tactic| ((try xstart); wp_simp +contextual))

--syntax "xwp" notFollowedBy("|") (ppSpace colGt term:max)* : tactic
--
--macro_rules
--  | `(tactic| xwp) => `(tactic| (try xstart; try (simp +contextual))) -- contextual needed in test_3 below. TODO: try with grind
--  | `(tactic| xwp $x $xs*) => `(tactic| (try xstart; try (simp +contextual); intro $x $xs*))

lemma focus_helper {p q : Prop} : p → (p ≤ q) → q := fun hp hpq => hpq hp

theorem bind_apply_2 {ps : PredShape} {α β : Type} (x : PredTrans ps α) (f : α → PredTrans ps β) (Q : PostCond β ps) :
  (bind x f).apply Q = x.apply (fun a => (f a).apply Q, Q.2) := by rfl

theorem imp_trans {p q r : Prop} : (p → q) → (q → r) → (p → r) := fun hpq hqr => hqr ∘ hpq

def focus_on_le_wp (goal : MVarId) : TacticM (MVarId × MVarId × Expr) := withMainContext do
  let tag ← goal.getTag
  let goal ← goal.betaReduce
  let tgt ← instantiateMVars (← goal.getDecl).type

  if tgt.isAppOf ``PredTrans.apply then
    -- goal is of the form (do ...).apply Q s₁ ... sₙ.
    -- apply focus_helper, get new goals ?p, ?p ≤ (do ...).apply Q s₁ ... sₙ
    let p::pq::gs ← liftMetaM <| goal.apply (mkConst ``focus_helper) | failure
    p.setTag tag
    pushGoals (pq::p::gs)
    let wp := tgt.getArg! 2
    return (pq, p, wp)

  -- Next, we apply le_trans to get two new goals
  --  · P s₁ ... sₙ ≤ ?H. This is going to be the new goal to be proved by the user.
  --  · ?H ≤ (do ...).apply Q s₁ ... sₙ. This is the "focus" and is going to be proved by the caller, for example by performing some rewrite.
  -- Additional complication: ≤ might already be simplified to →.
  let (lem, pred_trans_app) ←
    if tgt.isAppOf ``LE.le then pure (mkApp (mkConst ``le_trans [.zero]) (tgt.getArg! 0), tgt.getArg! 3)
    else if let .forallE _ _ b _ := tgt then pure (mkApp (mkConst ``le_trans [.zero]) (mkSort .zero), b)
    else throwError s!"xfocus: Not a valid target {tgt}"
  let pred_trans_app := pred_trans_app.headBeta
  unless pred_trans_app.isAppOf ``PredTrans.apply do
    throwError s!"xfocus: Not a predicate transformer application {pred_trans_app}"
  let wp := pred_trans_app.getArg! 2
  match_expr wp with
  | WP.wp _ _ _ _ _ => throwError s!"xfocus: Already focused on a wp⟦·⟧"
  | _ =>
  let g₁::g₂::gs ← liftMetaM <| goal.apply lem | failure
  g₁.setTag tag -- this is the rewritten main goal; copy tag
  pushGoals (g₂::g₁::gs)
  return (g₂, g₁, wp)

def xbind_tac (goal : MVarId) (wp : Expr) : TacticM Expr := withMainContext do
  match_expr wp with
  | Bind.bind _ _ _ _ _ _ =>
    let g::gs ← goal.apply (mkConst ``le_of_eq [.zero]) | throwError "xbind: le_of_eq yielded no goals"
    pushGoals (g::gs)
    let tgt ← instantiateMVars (← g.getDecl).type
    let res ← g.rewrite tgt (mkConst ``bind_apply_2)
    unless res.mvarIds.isEmpty do throwError "rewrite produced subgoals"
    let g ← g.replaceTargetEq res.eNew res.eqProof
    g.refl
    let_expr Eq _ _ r := (← instantiateMVars (← g.getDecl).type) | throwError "xbind: Refl but not an equality"
    return r
  | _ => throwError s!"xbind: Not a bind application {wp}"

syntax "xbind_no_dsimp" : tactic

elab "xbind_no_dsimp" : tactic => withMainContext do
  let (rw_goal, _user_goal, wp) ← focus_on_le_wp (← getMainGoal)
  let _wp ← xbind_tac rw_goal wp
  return

macro "xbind" : tactic => `(tactic| (xbind_no_dsimp; (try dsimp)))

def xapp_no_xbind (goal : MVarId) (spec : Option (TSyntax `term)) : TacticM Unit := withMainContext do
  let main_tag ← goal.getTag
  let tgt ← instantiateMVars (← goal.getDecl).type
  unless tgt.isAppOf ``PredTrans.apply do throwError s!"xapp: Not a PredTrans.apply application {tgt}"
  let wp := tgt.getArg! 2
  let_expr WP.wp m ps instWP α x := wp | throwError "xapp: Not a wp application {wp}"
--      let P ← liftMetaM <| mkFreshExprMVar (mkApp (mkConst ``PreCond) ps)
--      let Q ← liftMetaM <| mkFreshExprMVar (mkApp2 (mkConst ``PostCond) α ps)
--      let triple_ty ← mkAppM ``triple #[x, P, Q]
--      let spec_hole ← liftMetaM <| mkFreshExprMVar triple_ty (userName := `spec)
--      dbg_trace s!"triple_ty: {triple_ty}"
--      dbg_trace s!"spec_hole: {spec_hole}"
--      dbg_trace s!"spec_hole type: {← inferType spec_hole}"
--      let wp_apply_triple_app ← mkAppM ``wp_apply_triple #[spec_hole]
  -- dbg_trace s!"goal: {tgt}"
--  try
--    let triple_goal::main_goal::gs ← goal.apply (mkApp2 (mkConst ``wp_apply_triple) m ps) | failure
--    main_goal.setTag main_tag -- this is going to be the main goal after applying the triple
--    pushGoals (main_goal::gs)
--    apply_spec triple_goal -- first try without generalizing the postcondition
--  catch _ =>
  let triple_goal::post_goal::pre_goal::gs ← goal.apply (mkApp2 (mkConst ``wp_apply_triple_conseq) m ps) | failure
  post_goal.setTag main_tag -- this is going to be the main goal after applying the triple
  pre_goal.setTag `pre
  pushGoals (pre_goal::post_goal::gs)
  let triple_ty ← instantiateMVars (← triple_goal.getDecl).type
  if let some spec := spec then
    -- dbg_trace s!"spec: {spec}"
    let spec ← elabTerm spec triple_ty
    -- dbg_trace s!"spec: {spec}"
    let gs ← triple_goal.apply spec
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
        let gs ← triple_goal.apply (mkConst specs[0]!)
        pushGoals gs
        pruneSolvedGoals
    else
      throwError s!"not an application of a constant: {x}"
  try let _ ← post_goal.apply (mkConst ``le_refl [.zero]) catch _ => pure ()

syntax "xapp_no_xbind" (ppSpace colGt term)? : tactic

elab "xapp_no_xbind" spec:optional(term) : tactic => withMainContext do
  xapp_no_xbind (← getMainGoal) spec

syntax "xapp_no_simp" (ppSpace colGt term)? : tactic

-- or: xspec
syntax "xapp" (ppSpace colGt term)? : tactic
macro_rules
  | `(tactic| xapp_no_simp)       => `(tactic| ((try xbind); xapp_no_xbind))
  | `(tactic| xapp_no_simp $spec) => `(tactic| ((try xbind); xapp_no_xbind $spec))
  | `(tactic| xapp)               => `(tactic| xapp_no_simp <;> try simp +contextual only [gt_iff_lt, Prod.mk_le_mk, le_refl, and_true])
  | `(tactic| xapp $spec)         => `(tactic| xapp_no_simp $spec <;> try simp +contextual only [gt_iff_lt, Prod.mk_le_mk, le_refl, and_true])

macro "sgrind" : tactic => `(tactic| ((try simp +contextual); grind))

theorem test_ex :
  ⦃fun s => s = 4⦄
  do
    let mut x := 0
    let s ← get
    for i in [1:s] do { x := x + i; if x > 4 then throw 42 }
    (set 1 : ExceptT Nat (StateT Nat Idd) PUnit)
    return x
  ⦃(fun r s => False,
    fun e s => e = 42 ∧ s = 4,
    ())⦄ := by
  xstart
  intro s hs
  xwp
  -- xbind -- optional
  xapp (Specs.forIn_list (fun (r, xs) s => r ≤ 4 ∧ s = 4 ∧ r + xs.suff.sum > 4, fun e s => e = 42 ∧ s = 4, ()) ?step)
  case pre => simp only [hs]; conv in (List.sum _) => { whnf }; simp
  case step =>
    intro hd tl _ _ b
    xstart
    xwp
    simp only [List.sum_cons, List.sum_nil, add_zero]
    intro b' hinv
    split
    · grind -- simp[hinv, h]
    · simp only [PredTrans.pure_apply]; sorry -- grind -- omega
  simp only [List.sum_nil, add_zero]
  sorry -- grind

end MPL
