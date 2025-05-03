/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
import MPL.WP
import MPL.MonadMorphism

/-!
# Monad morphisms and weakest precondition interpretations

A `WP m ps` is a `WPMonad m ps` if the interpretation `WP.wp` is also a `MonadMorphism`.
-/

namespace MPL
open MPL

universe u
variable {m : Type → Type u} {ps : PostShape}

/--
  A `WP` that is also a `MonadMorphism`. (They all are.)
-/
class WPMonad (m : Type → Type u) (ps : outParam PostShape) [Monad m]
  extends LawfulMonad m, WP m ps, MonadMorphism m (PredTrans ps) wp where

theorem WP.pure_apply [Monad m] [WPMonad m ps] (a : α) (Q : PostCond α ps) :
  wp⟦pure (f:=m) a⟧.apply Q = let x := a; Q.1 x := by
    simp only [pure_pure, PredTrans.pure_apply]

theorem WP.bind_apply [Monad m] [WPMonad m ps] (x : m α) (f : α → m β) (Q : PostCond β ps) :
  wp⟦x >>= f⟧.apply Q = wp⟦x⟧.apply (fun a => wp⟦f a⟧.apply Q, Q.2) := by
    simp only [bind_bind, PredTrans.bind_apply]

theorem WP.map_apply [Monad m] [WPMonad m ps] (f : α → β) (x : m α) (Q : PostCond β ps) :
  wp⟦f <$> x⟧.apply Q = wp⟦x⟧.apply (fun a => Q.1 (f a), Q.2) := by
    simp only [map_map, PredTrans.map_apply]

theorem WP.seq_apply [Monad m] [WPMonad m ps] (f : m (α → β)) (x : m α) (Q : PostCond β ps) :
  wp⟦f <*> x⟧.apply Q = wp⟦f⟧.apply (fun f => wp⟦x⟧.apply (fun a => Q.1 (f a), Q.2), Q.2) := by
    simp only [seq_seq, PredTrans.seq_apply]

theorem WP.morph_pure_apply [Monad m] [Monad n] [LawfulMonad m] [MonadMorphism m n morph] [WPMonad n ps]
  (a : α) (Q : PostCond α ps) :
  wp⟦morph (pure a) : n α⟧.apply Q = wp⟦pure a : n α⟧.apply Q := by
    simp only [pure_pure]

theorem WP.morph_bind_apply [Monad m] [Monad n] [LawfulMonad m] [MonadMorphism m n morph] [WPMonad n ps]
  (x : m α) (f : α → m β) (Q : PostCond β ps) :
  wp⟦morph (x >>= f) : n β⟧.apply Q = wp⟦morph x >>= fun a => morph (f a) : n β⟧.apply Q := by
    simp only [bind_bind]

theorem WP.morph_map_apply [Monad m] [Monad n] [LawfulMonad m] [MonadMorphism m n morph] [WPMonad n ps]
  (f : α → β) (x : m α) (Q : PostCond β ps) :
  wp⟦morph (f <$> x) : n β⟧.apply Q = wp⟦f <$> morph x : n β⟧.apply Q := by
    simp only [map_map]

theorem WP.morph_seq_apply [Monad m] [Monad n] [LawfulMonad m] [MonadMorphism m n morph] [WPMonad n ps]
  (f : m (α → β)) (x : m α) (Q : PostCond β ps) :
  wp⟦morph (f <*> x) : n β⟧.apply Q = wp⟦morph f <*> morph x : n β⟧.apply Q := by
    simp only [seq_seq]

theorem WP.morph_dite_apply {ps} {Q : PostCond α ps} (c : Prop) [Decidable c] [Monad m] [Monad n] [MonadMorphism m n morph] [WP n ps] (t : c → m α) (e : ¬ c → m α) :
  wp⟦morph (if h : c then t h else e h)⟧.apply Q = if h : c then wp⟦morph (t h)⟧.apply Q else wp⟦morph (e h)⟧.apply Q := by split <;> rfl

theorem WP.morph_ite_apply {ps} {Q : PostCond α ps} (c : Prop) [Decidable c] [Monad m] [Monad n] [MonadMorphism m n morph] [WP n ps] (t : m α) (e : m α) :
  wp⟦morph (if c then t else e)⟧.apply Q = if c then wp⟦morph t⟧.apply Q else wp⟦morph e⟧.apply Q := by split <;> rfl

instance Idd.instWPMonad : WPMonad Idd .pure where
  pure_pure a := by ext; simp only [wp, Idd.run_pure, instMonadPredTrans]
  bind_bind x f := by ext; simp only [wp, PredTrans.pure, Bind.bind, Idd.bind, PredTrans.bind]

instance Id.instWPMonad : WPMonad Id .pure where
  pure_pure a := by simp only [wp, PredTrans.pure, Pure.pure, Id.run]
  bind_bind x f := by simp only [wp, PredTrans.pure, Bind.bind, Id.run, PredTrans.bind]

instance StateT.instWPMonad [Monad m] [WPMonad m ps] : WPMonad (StateT σ m) (.arg σ ps) where
  pure_pure a := by ext; simp only [wp, pure, StateT.pure, pure_pure, PredTrans.pure,
    PredTrans.pushArg_apply]
  bind_bind x f := by ext; simp only [wp, bind, StateT.bind, bind_bind, PredTrans.bind,
    PredTrans.pushArg_apply]

instance ReaderT.instWPMonad [Monad m] [WPMonad m ps] : WPMonad (ReaderT ρ m) (.arg ρ ps) where
  pure_pure a := by ext; simp only [wp, pure, ReaderT.pure, pure_pure, PredTrans.pure,
    PredTrans.pushArg_apply, PredTrans.map_apply]
  bind_bind x f := by ext; simp only [wp, bind, ReaderT.bind, bind_bind, PredTrans.bind,
    PredTrans.pushArg_apply, PredTrans.map_apply]

instance ExceptT.instWPMonad [Monad m] [WPMonad m ps] : WPMonad (ExceptT ε m) (.except ε ps) where
  pure_pure a := by ext; simp only [wp, pure, ExceptT.pure, ExceptT.mk, pure_pure, PredTrans.pure,
    PredTrans.pushExcept_apply]
  bind_bind x f := by
    ext Q
    simp only [wp, bind, ExceptT.bind, ExceptT.mk, bind_bind, PredTrans.bind, ExceptT.bindCont,
      PredTrans.pushExcept_apply]
    congr
    ext b
    cases b
    case error a => simp [PredTrans.pure, pure]
    case ok a => rfl

instance EStateM.instWPMonad : WPMonad (EStateM ε σ) (.except ε (.arg σ .pure)) where
  pure_pure a := by simp only [wp, pure, EStateM.pure, PredTrans.pure]
  bind_bind x f := by
    ext Q : 2
    simp [wp, bind, EStateM.bind, eq_iff_iff, PredTrans.bind]
    ext s : 1
    cases (x s) <;> simp

instance Except.instWPMonad : WPMonad (Except ε) (.except ε .pure) where
  pure_pure a := rfl
  bind_bind x f := by cases x <;> rfl

instance State.instWPMonad : WPMonad (StateM σ) (.arg σ .pure) :=
  inferInstanceAs (WPMonad (StateT σ Id) (.arg σ .pure))
instance Reader.instWPMonad : WPMonad (ReaderM ρ) (.arg ρ .pure) :=
  inferInstanceAs (WPMonad (ReaderT ρ Id) (.arg ρ .pure))
