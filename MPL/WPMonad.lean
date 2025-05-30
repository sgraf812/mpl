/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
import MPL.WP

/-!
# Monad morphisms and weakest precondition interpretations

A `WP m ps` is a `WPMonad m ps` if the interpretation `WP.wp` is also a monad morphism, that is,
it preserves `pure` and `bind`.
-/

namespace MPL
open MPL

universe u
variable {m : Type → Type u} {ps : PostShape}

/--
  A `WP` that is also a monad morphism, preserving `pure` and `bind`. (They all are.)
-/
class WPMonad (m : Type → Type u) (ps : outParam PostShape) [Monad m]
  extends LawfulMonad m, WP m ps where
  wp_pure : ∀ {α} (a : α), wp (pure a) = pure a
  wp_bind : ∀ {α β} (x : m α) (f : α → m β), wp (do let a ← x; f a) = do let a ← wp x; wp (f a)

attribute [simp] WPMonad.wp_pure WPMonad.wp_bind

@[simp]
theorem WPMonad.wp_map [Monad m] [WPMonad m ps] (f : α → β) (x : m α) :
  wp (f <$> x) = f <$> wp x := by
    simp [← bind_pure_comp, wp_bind, wp_pure]

@[simp]
theorem WPMonad.wp_seq [Monad m] [WPMonad m ps] (f : m (α → β)) (x : m α) :
  wp (f <*> x) = wp f <*> wp x := by
    simp [← bind_map, wp_bind, wp_map]

@[simp]
theorem WPMonad.wp_dite {c : Prop} [Decidable c] {t : c → m α} {e : ¬c → m α} [Monad m] [WPMonad m ps] :
  wp (dite c t e) = if h : c then wp (t h) else wp (e h) := by
    split <;> simp

@[simp]
theorem WPMonad.wp_ite {c : Prop} [Decidable c] {t : m α} {e : m α} [Monad m] [WPMonad m ps] :
  wp (ite c t e) = if c then wp t else wp e := by
  split <;> simp

theorem WPMonad.pure_apply [Monad m] [WPMonad m ps] (a : α) (Q : PostCond α ps) :
  wp⟦pure (f:=m) a⟧ Q = Q.1 a := by
    simp only [wp_pure, PredTrans.pure_apply]

theorem WPMonad.bind_apply [Monad m] [WPMonad m ps] (x : m α) (f : α → m β) (Q : PostCond β ps) :
  wp⟦x >>= f⟧ Q = wp⟦x⟧ (fun a => wp⟦f a⟧ Q, Q.2) := by
    simp only [wp_bind, PredTrans.bind_apply]

theorem WPMonad.map_apply [Monad m] [WPMonad m ps] (f : α → β) (x : m α) (Q : PostCond β ps) :
  wp⟦f <$> x⟧ Q = wp⟦x⟧ (fun a => Q.1 (f a), Q.2) := by
    simp only [wp_map, PredTrans.map_apply]

theorem WPMonad.seq_apply [Monad m] [WPMonad m ps] (f : m (α → β)) (x : m α) (Q : PostCond β ps) :
  wp⟦f <*> x⟧ Q = wp⟦f⟧ (fun f => wp⟦x⟧ (fun a => Q.1 (f a), Q.2), Q.2) := by
    simp only [wp_seq, PredTrans.seq_apply]

theorem WPMonad.dite_apply {ps} {Q : PostCond α ps} (c : Prop) [Decidable c] [Monad m] [WPMonad m ps] (t : c → m α) (e : ¬ c → m α) :
  wp⟦if h : c then t h else e h⟧ Q = if h : c then wp⟦t h⟧ Q else wp⟦e h⟧ Q := by split <;> rfl

theorem WPMonad.ite_apply {ps} {Q : PostCond α ps} (c : Prop) [Decidable c] [Monad m] [WPMonad m ps] (t : m α) (e : m α) :
  wp⟦if c then t else e⟧ Q = if c then wp⟦t⟧ Q else wp⟦e⟧ Q := by split <;> rfl

open WPMonad

instance Idd.instWPMonad : WPMonad Idd .pure where
  wp_pure a := by ext; simp only [wp, Idd.run_pure, instMonadPredTrans]
  wp_bind x f := by ext; simp only [wp, PredTrans.pure, Bind.bind, Idd.bind, PredTrans.bind]

instance Id.instWPMonad : WPMonad Id .pure where
  wp_pure a := by simp only [wp, PredTrans.pure, Pure.pure, Id.run]
  wp_bind x f := by simp only [wp, PredTrans.pure, Bind.bind, Id.run, PredTrans.bind]

instance StateT.instWPMonad [Monad m] [WPMonad m ps] : WPMonad (StateT σ m) (.arg σ ps) where
  wp_pure a := by ext; simp only [wp, pure, StateT.pure, WPMonad.wp_pure, PredTrans.pure,
    PredTrans.pushArg_apply]
  wp_bind x f := by ext; simp only [wp, bind, StateT.bind, WPMonad.wp_bind, PredTrans.bind,
    PredTrans.pushArg_apply]

instance ReaderT.instWPMonad [Monad m] [WPMonad m ps] : WPMonad (ReaderT ρ m) (.arg ρ ps) where
  wp_pure a := by ext; simp only [wp, pure, ReaderT.pure, WPMonad.wp_pure, PredTrans.pure,
    PredTrans.pushArg_apply, PredTrans.map_apply]
  wp_bind x f := by ext; simp only [wp, bind, ReaderT.bind, WPMonad.wp_bind, PredTrans.bind,
    PredTrans.pushArg_apply, PredTrans.map_apply]

instance ExceptT.instWPMonad [Monad m] [WPMonad m ps] : WPMonad (ExceptT ε m) (.except ε ps) where
  wp_pure a := by ext; simp only [wp, pure, ExceptT.pure, ExceptT.mk, WPMonad.wp_pure,
    PredTrans.pure, PredTrans.pushExcept_apply]
  wp_bind x f := by
    ext Q
    simp only [wp, bind, ExceptT.bind, ExceptT.mk, WPMonad.wp_bind, PredTrans.bind,
      ExceptT.bindCont, PredTrans.pushExcept_apply]
    congr
    ext b
    cases b
    case error a => simp [PredTrans.pure, pure]
    case ok a => rfl

instance EStateM.instWPMonad : WPMonad (EStateM ε σ) (.except ε (.arg σ .pure)) where
  wp_pure a := by simp only [wp, pure, EStateM.pure, PredTrans.pure]
  wp_bind x f := by
    ext Q : 2
    simp [wp, bind, EStateM.bind, eq_iff_iff, PredTrans.bind]
    ext s : 1
    cases (x s) <;> simp

instance Except.instWPMonad : WPMonad (Except ε) (.except ε .pure) where
  wp_pure a := rfl
  wp_bind x f := by cases x <;> rfl

instance State.instWPMonad : WPMonad (StateM σ) (.arg σ .pure) :=
  inferInstanceAs (WPMonad (StateT σ Id) (.arg σ .pure))
instance Reader.instWPMonad : WPMonad (ReaderM ρ) (.arg ρ .pure) :=
  inferInstanceAs (WPMonad (ReaderT ρ Id) (.arg ρ .pure))
