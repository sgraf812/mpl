/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
import MPL.ProofMode.Tactics.Basic
import MPL.WPSimp
import MPL.WP
import MPL.WPMonad
import MPL.WPMonadLift
import MPL.WPMonadFunctor
import MPL.WPMonadExceptOf

namespace MPL.ProofMode.Tactics
open Lean Elab Tactic Meta

elab "mwp" : tactic => do
  let mvar ← getMainGoal
  let some _ := parseMGoal? (← instantiateMVars <| ← mvar.getType) | throwError "mwp: not in proof mode"
  -- Somehow, conv in ... => rfl breaks the use of `withCollectingNewGoalsFrom` in `mspec`.
  -- I won't investigate because wp_simp will be replaced anyway.
  --  let (mvars, _) ← runTactic mvar (← `(tactic| conv in SPred.entails _ _ => arg 2; tactic => wp_simp))
  let (mvars, _) ← runTactic mvar (← `(tactic| wp_simp))
  replaceMainGoal mvars

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
  eq_self
  SPred.imp_self_simp
  SPred.true_intro_simp
  SPred.true_intro_simp_nil
  PostCond.entails FailConds.entails_false FailConds.entails_refl FailConds.entails_true FailConds.pure_def SPred.entails.refl
  -- Lawful monad normalization that we don't appear to be needing!
  -- bind_pure_comp map_pure id_map' ExceptT.map_throw bind_map bind_map_left bind_pure pure_bind bind_assoc
  -- MonadMorphism and basic if/then/else:
  WP.pure_apply WP.bind_apply WP.map_apply WP.seq_apply
  WP.ite_apply WP.dite_apply
  WP.morph_pure_apply WP.morph_bind_apply WP.morph_map_apply WP.morph_seq_apply
  WP.morph_ite_apply WP.morph_dite_apply
  -- MonadLift implementation
  StateT.monadLift_apply ReaderT.monadLift_apply ExceptT.monadLift_apply
--  PredTrans.monadLiftArg_apply PredTrans.monadLiftExcept_apply
  -- MonadLiftT implementation
  MonadLiftT.monadLift_trans_apply MonadLiftT.monadLift_refl_apply
  -- MonadFunctor implementation
  StateT.monadMap_apply ReaderT.monadMap_apply ExceptT.monadMap_apply
--  PredTrans.monadMapArg_apply PredTrans.monadMapExcept_apply
--  WP.popArg_StateT_wp WP.popArg_ReaderT_wp WP.popExcept_ExceptT_wp
  WP.ReaderT_run_apply WP.StateT_run_apply WP.ExceptT_run_apply
  -- List.Zipper.begin_suff List.Zipper.tail_suff List.Zipper.end_suff -- Zipper stuff needed for invariants
  Std.Range.forIn_eq_forIn_range' Std.Range.forIn'_eq_forIn'_range' Std.Range.size Nat.div_one  -- rewrite to forIn_list
  Array.forIn_eq_forIn_toList Array.forIn'_eq_forIn'_toList -- rewrite to forIn_list
  -- state, reader, except ..Of impls
  StateT.get_apply
  StateT.set_apply
  StateT.modifyGet_apply
  ReaderT.read_apply
  ReaderT.withReader_apply
  ExceptT.throw_apply
  ExceptT.tryCatch_apply
  Except.throw_apply
  Except.tryCatch_apply
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
