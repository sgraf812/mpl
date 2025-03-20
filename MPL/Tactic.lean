import Lean
import MPL.Triple
import MPL.SpecAttr

import MPL.Specs
import MPL.WPMonad
import MPL.WPMonadLift
import MPL.WPMonadFunctor
import MPL.WPMonadExceptOf
import MPL.WPSimp
import Mathlib

namespace MPL

open Lean Meta Elab Tactic

theorem wp_apply_triple_conseq {m : Type → Type} {ps : PredShape} [WP m ps] {α} {x : m α} {P : PreCond ps} {Q Q' : PostCond α ps}
  (h : ⦃P⦄ x ⦃Q⦄) (hpost : Q ≤ Q') :
  P ≤ wp⟦x⟧.apply Q' := le_trans h (wp⟦x⟧.mono _ _ hpost)

macro "xstart" : tactic => `(tactic| unfold triple)

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
  refl
  -- Lawful monad normalization that we don't appear to be needing!
  -- bind_pure_comp map_pure id_map' ExceptT.map_throw bind_map bind_map_left bind_pure pure_bind bind_assoc
  -- MonadMorphism and basic if/then/else:
  WP.pure_apply WP.bind_apply WP.map_apply WP.seq_apply
  WP.ite_apply WP.dite_apply
  -- MonadLift implementation
  WP.monadLift_pure_apply WP.monadLift_bind_apply WP.monadLift_map_apply WP.monadLift_seq_apply
  WP.monadLift_apply PredTrans.monadLiftArg_apply PredTrans.monadLiftExcept_apply
  -- MonadLiftT implementation
  MonadLiftT.monadLift_trans_apply MonadLiftT.monadLift_refl_apply
  -- MonadFunctor implementation
  WP.monadMap_apply PredTrans.monadMapArg_apply PredTrans.monadMapExcept_apply
  WP.popArg_StateT_wp WP.popArg_ReaderT_wp WP.popExcept_ExceptT_wp WP.ReaderT_run_apply WP.StateT_run_apply WP.ExceptT_run_apply
  WP.wp1_apply
  -- List.Zipper.begin_suff List.Zipper.tail_suff List.Zipper.end_suff -- Zipper stuff needed for invariants
  Std.Range.forIn_eq_forIn_range' Std.Range.forIn'_eq_forIn'_range' Std.Range.size Nat.div_one  -- rewrite to forIn_list
  Array.forIn_eq_forIn_toList Array.forIn'_eq_forIn'_toList -- rewrite to forIn_list
  -- ite_extrude_yield List.forIn_yield_eq_foldlM -- rewrite to foldlM. Needs some of the LawfulMonad normalization laws as well; benefit of doing this is unclear
  -- ←List.forIn_yield_eq_foldlM syntax not supported (yet)?
  -- state, reader, except ..Of impls
  StateT.get_apply
  StateT.set_apply
  StateT.modifyGet_apply
  ReaderT.read_apply
  ReaderT.withReader_apply
  ExceptT.throw_apply
  ExceptT.tryCatch_apply
  -- lifting state
  MonadStateOf.get_apply MonadStateOf.getThe_apply MonadState.get_apply
  MonadStateOf.set_apply MonadState.set_apply
  MonadStateOf.modifyGet_apply MonadStateOf.modifyGetThe_apply MonadState.modifyGet_apply
  MonadStateOf.modify_apply MonadStateOf.modifyThe_apply
  -- lifting reader
  MonadReaderOf.read_apply MonadReaderOf.readThe_apply MonadReader.read_apply
  MonadWithReaderOf.withReader_apply MonadWithReaderOf.withTheReader_apply MonadWithReader.withReader_apply
  -- lifting except (none yet; requires a bunch of lemmas per ReaderT, StateT, ExceptT, etc.)
  MonadExcept.throw_apply MonadExcept.throwThe_apply
  ReaderT.throw_apply StateT.throw_apply ExceptT.lift_throw_apply
  MonadExcept.tryCatch_apply MonadExcept.tryCatchThe_apply
  ReaderT.tryCatch_apply StateT.tryCatch_apply ExceptT.lift_tryCatch_apply

macro "xwp" : tactic =>
  `(tactic| ((try unfold triple); wp_simp))

macro "xpure" : tactic =>
  `(tactic| with_reducible (conv in PredTrans.apply (WP.wp (pure _)) _ => apply WP.pure_apply))

macro "xbind" : tactic =>
  `(tactic| with_reducible (conv in PredTrans.apply (WP.wp (_ >>= _)) _ => apply WP.bind_apply))

def xapp_no_xbind (goal : MVarId) (spec : Option (TSyntax `term)) : TacticM Unit := withMainContext do
  let main_tag ← goal.getTag
  let tgt ← instantiateMVars (← goal.getDecl).type
  let tgt := tgt.consumeMData -- had the error below trigger in Lean4Lean for some reason
  unless tgt.isAppOf ``PredTrans.apply do throwError s!"xapp: Not a PredTrans.apply application {tgt}"
  let wp := tgt.getArg! 2
  let_expr WP.wp m ps instWP α x := wp | throwError "xapp: Not a wp application {wp}"
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
        let gs ← triple_goal.apply (← mkConstWithFreshMVarLevels specs[0]!)
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
    intro b _rpref x suff _h
    xstart
    xwp
    simp only [List.sum_cons, List.sum_nil, add_zero]
    intro b' hinv
    split
    · grind -- simp[hinv, h]
    · omega -- grind
  simp only [List.sum_nil, add_zero]
  sorry -- grind -- needs 4.17 lemmas

end MPL
