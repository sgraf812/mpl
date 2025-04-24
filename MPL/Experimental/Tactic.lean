import Lean
import MPL.Triple
import MPL.SpecAttr

import MPL.Specs
import MPL.WPMonad
import MPL.WPMonadLift
import MPL.WPMonadFunctor
import MPL.WPMonadExceptOf
import MPL.WPSimp
import MPL.ProofMode

namespace MPL

open Lean Meta Elab Tactic

theorem wp_apply_triple_conseq {m : Type → Type} {ps : PredShape} [WP m ps] {α} {x : m α} {P : PreCond ps} {Q Q' : PostCond α ps}
  (h : ⦃P⦄ x ⦃Q⦄) (hpost : SPred.entails (wp⟦x⟧.apply Q) (wp⟦x⟧.apply Q')) :
  P.entails (wp⟦x⟧.apply Q') := SPred.entails.trans h hpost

theorem wp_apply_triple_conseq_mono {m : Type → Type} {ps : PredShape} [WP m ps] {α} {x : m α} {P : PreCond ps} {Q Q' : PostCond α ps}
  (h : ⦃P⦄ x ⦃Q⦄) (hpost : Q.entails Q') :
  P.entails (wp⟦x⟧.apply Q') := wp_apply_triple_conseq h (wp⟦x⟧.mono _ _ hpost)

macro "xstart" : tactic => `(tactic| unfold triple)

theorem ite_extrude_yield {c : Prop} [Decidable c] {x y : α} :
  (if c then pure (.yield x) else pure (.yield y)) = ForInStep.yield <$> if c then pure x else pure (f := Idd) y := by
  split <;> simp

macro "xwp" : tactic =>
  `(tactic| ((try unfold triple); wp_simp))

macro "xpure" : tactic =>
  `(tactic| with_reducible (conv in PredTrans.apply (WP.wp (pure _)) _ => apply WP.pure_apply))

macro "xbind" : tactic =>
  `(tactic| with_reducible (conv in PredTrans.apply (WP.wp (_ >>= _)) _ => apply WP.bind_apply))

def xapp_n_no_xbind (goal : MVarId) (spec : Option (TSyntax `term)) (thm : Name) : TacticM Unit := withMainContext do
  let main_tag ← goal.getTag
  let tgt ← instantiateMVars (← goal.getDecl).type
  let tgt := tgt.consumeMData -- had the error below trigger in Lean4Lean for some reason
  unless tgt.isAppOf ``PredTrans.apply do throwError s!"xapp: Not a PredTrans.apply application {tgt}"
  let wp := tgt.getArg! 2
  let_expr WP.wp m ps instWP α x := wp | throwError "xapp: Not a wp application {wp}"
  let triple_goal::post_goal::pre_goal::gs ← goal.apply (mkApp2 (mkConst thm) m ps) | failure
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
        let gs ← triple_goal.apply (← mkConstWithFreshMVarLevels specs[0]!)
        pushGoals gs
        pruneSolvedGoals
    else
      throwError s!"not an application of a constant: {x}"
  try let _ ← post_goal.apply (mkConst ``PostCond.entails_refl) catch _ => pure ()

syntax "xapp_no_xbind" (ppSpace colGt term)? : tactic

elab "xapp_no_xbind" spec:optional(term) : tactic => withMainContext do
  xapp_n_no_xbind (← getMainGoal) spec ``wp_apply_triple_conseq_mono

syntax "xapp_no_simp" (ppSpace colGt term)? : tactic

-- or: xspec
syntax "xapp" (ppSpace colGt term)? : tactic
macro_rules
  | `(tactic| xapp_no_simp)       => `(tactic| ((try xbind); xapp_no_xbind))
  | `(tactic| xapp_no_simp $spec) => `(tactic| ((try xbind); xapp_no_xbind $spec))
  | `(tactic| xapp)               => `(tactic| xapp_no_simp <;> try simp +contextual only [gt_iff_lt, Prod.mk_le_mk, le_refl, and_true, PostCond.entails, FailConds.entails_false, FailConds.entails_refl, FailConds.entails_true, FailConds.pure_def, SPred.entails.refl, *])
  | `(tactic| xapp $spec)         => `(tactic| xapp_no_simp $spec <;> ((try simp +contextual only [gt_iff_lt, Prod.mk_le_mk, le_refl, and_true, PostCond.entails, FailConds.entails_false, FailConds.entails_refl, FailConds.entails_true, FailConds.pure_def, SPred.entails.refl, *]); try (guard_target = (_ : Prop); trivial)))

elab "xapp2_no_xbind" spec:optional(term) : tactic => withMainContext do
  xapp_n_no_xbind (← getMainGoal) spec ``wp_apply_triple_conseq

syntax "xapp2_no_simp" (ppSpace colGt term)? : tactic

-- or: xspec
syntax "xapp2" (ppSpace colGt term)? : tactic
macro_rules
  | `(tactic| xapp2_no_simp)       => `(tactic| ((try xbind); xapp2_no_xbind))
  | `(tactic| xapp2_no_simp $spec) => `(tactic| ((try xbind); xapp2_no_xbind $spec))
  | `(tactic| xapp2)               => `(tactic| xapp2_no_simp <;> try simp +contextual only [gt_iff_lt, Prod.mk_le_mk, le_refl, and_true])
  | `(tactic| xapp2 $spec)         => `(tactic| xapp2_no_simp $spec <;> try simp +contextual only [gt_iff_lt, Prod.mk_le_mk, le_refl, and_true])

macro "sgrind" : tactic => `(tactic| ((try simp +contextual); grind))

example :
  ⦃fun s => s = 4⦄
  do
    let mut x := 0
    let s ← get
    for i in [1:s] do { x := x + i; if x > 4 then throw 42 }
    (set 1 : ExceptT Nat (StateT Nat Idd) PUnit)
    return x
  ⦃post⟨fun r s => False, fun e s => e = 42 ∧ s = 4⟩⦄ := by
  intro s hs
  xwp
  -- xbind -- optional
  xapp (Specs.forIn_list ↑⟨fun (r, xs) s => r ≤ 4 ∧ s = 4 ∧ r + xs.suff.sum > 4, fun e s => e = 42 ∧ s = 4, ()⟩ ?step)
  case pre => simp only [hs]; decide
  case step =>
    intro b _rpref x suff _h
    xstart
    xwp
    simp only [List.sum_cons, List.sum_nil]
    intro b' hinv
    split
    · grind -- simp [hinv, h]
    · omega -- grind
  simp only [List.sum_nil]
  sorry -- grind -- needs 4.17 lemmas

example :
  ⦃fun s => s = 4⦄
  do
    let mut x := 0
    let s ← get
    for i in [1:s] do { x := x + i; if x > 4 then throw 42 }
    (set 1 : ExceptT Nat (StateT Nat Idd) PUnit)
    return x
  ⦃post⟨fun r s => False,
        fun e s => e = 42 ∧ s = 4⟩⦄ := by
  mintro h ∀s
  mpure h
  subst h
  mwp
  mspec (Specs.forIn_list ↑⟨fun (r, xs) s => r ≤ 4 ∧ s = 4 ∧ r + xs.suff.sum > 4, fun e s => e = 42 ∧ s = 4, ()⟩ ?step)
  case step =>
    intro b _rpref x suff _h
    mintro hinv ∀s
    mpure hinv
    mwp
    simp_all only [List.sum_cons, List.sum_nil, ite_app]
    split
    · trivial
    · simp_all only [PredShape.args, SVal.curry_nil, true_and,
      SPred.entails_nil, forall_const]; omega -- grind
  simp only [List.sum_nil]
  sorry -- grind -- needs 4.17 lemmas

syntax "CHONK_trivial" : tactic
macro_rules | `(tactic| CHONK_trivial) => `(tactic| trivial)

syntax (name := CHONK) "CHONK" optional("[" Lean.Parser.Tactic.simpLemma,+ "]") : tactic
macro_rules
  | `(tactic| CHONK) => `(tactic| CHONK[if_true_left]) -- if_true_left is redundant, but empty list did not work for some reason.
  | `(tactic| CHONK [$args,*]) => `(tactic| (intros; first
    | (intro; repeat intro) -- expand ≤ on → and PreConds, also turns triple goals into wp goals
    | CHONK_trivial
    | xapp
    | xwp
    | simp_all only [if_true_left, if_false_left, and_self, and_true, List.length_nil, List.length_cons, ne_eq, not_false_eq_true, gt_iff_lt
        , reduceIte
        , Nat.sub_one_add_one
      ]
    | (simp_all [$args,*, Nat.sub_one_add_one]; done)
    -- | grind
    ))

--  `(tactic| ((try intros); xstart; intro h; xwp; try (all_goals simp_all)))
--  `(tactic| sorry)

end MPL
