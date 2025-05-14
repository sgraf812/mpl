/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
import MPL.Triple
import MPL.WP
import MPL.WPMonad
import MPL.WPMonadLift
import MPL.WPMonadFunctor
import MPL.WPMonadExceptOf
import MPL.SpecAttr

/-!
# Hoare triple specifications for select functions

This module contains Hoare triple specifications for some functions in Core.
-/

namespace Std.Range

abbrev toList (r : Std.Range) : List Nat :=
  List.range' r.start ((r.stop - r.start + r.step - 1) / r.step) r.step

end Std.Range

namespace MPL

namespace List

@[ext]
structure Zipper {α : Type u} (l : List α) : Type u where
  rpref : List α
  suff : List α
  property : rpref.reverse ++ suff = l

abbrev Zipper.pref {α} {l : List α} (s : List.Zipper l) : List α := s.rpref.reverse

abbrev Zipper.begin (l : List α) : Zipper l := ⟨[],l,rfl⟩
abbrev Zipper.end (l : List α) : Zipper l := ⟨l.reverse,[],by simp⟩
abbrev Zipper.tail (s : Zipper l) (h : s.suff = hd::tl) : Zipper l :=
  { rpref := hd::s.rpref, suff := tl, property := by simp [s.property, ←h] }

@[simp]
theorem Zipper.begin_eq_end_iff_nil {l : List α} : Zipper.begin l = Zipper.end l ↔ l = [] := by
  constructor <;> simp [begin, Zipper.end]

@[simp]
theorem Zipper.nil_begin_eq_end : Zipper.begin ([] : List α) = Zipper.end ([] : List α) := rfl

@[simp]
theorem Zipper.begin_suff {l : List α} : (Zipper.begin l).suff = l := rfl

@[simp]
theorem Zipper.begin_pref {l : List α} : (Zipper.begin l).pref = [] := rfl

@[simp]
theorem Zipper.end_pref {l : List α} : (Zipper.end l).pref = l := by simp [Zipper.end,pref]

@[simp]
theorem Zipper.end_suff {l : List α} : (Zipper.end l).suff = [] := rfl

@[simp]
theorem Zipper.tail_suff {l : List α} {s : Zipper l} (h : s.suff = hd::tl) : (s.tail h).suff = tl := rfl

end List

/-! # If/Then/Else -/

@[spec]
theorem Specs.ite {α m ps} {P : Assertion ps} {Q : PostCond α ps} (c : Prop) [Decidable c] [WP m ps] (t : m α) (e : m α)
    (ifTrue : c → ⦃P⦄ t ⦃Q⦄) (ifFalse : ¬c → ⦃P⦄ e ⦃Q⦄) :
    ⦃P⦄ if c then t else e ⦃Q⦄ := by
  split <;> apply_rules

@[spec]
theorem Specs.dite {α m ps} {P : Assertion ps} {Q : PostCond α ps} (c : Prop) [Decidable c] [WP m ps] (t : c → m α) (e : ¬ c → m α)
    (ifTrue : (h : c) → ⦃P⦄ t h ⦃Q⦄) (ifFalse : (h : ¬ c) → ⦃P⦄ e h ⦃Q⦄) :
    ⦃P⦄ if h : c then t h else e h ⦃Q⦄ := by
  split <;> apply_rules

/-! # `Monad` -/

universe u
variable {m : Type → Type u} {ps : PostShape}

theorem Specs.pure' [Monad m] [WPMonad m ps] {P : Assertion ps} {Q : PostCond α ps}
    (h : P ⊢ₛ Q.1 a) :
    ⦃P⦄ Pure.pure (f:=m) a ⦃Q⦄ := Triple.pure a h

@[spec]
theorem Specs.pure {m : Type → Type u} {ps : PostShape} [Monad m] [WPMonad m ps] {α} {a : α} {Q : PostCond α ps} :
  ⦃Q.1 a⦄ Pure.pure (f:=m) a ⦃Q⦄ := Specs.pure' .rfl

theorem Specs.bind' [Monad m] [WPMonad m ps] {x : m α} {f : α → m β} {P : Assertion ps} {Q : PostCond β ps}
    (h : ⦃P⦄ x ⦃(fun a => wp⟦f a⟧ Q, Q.2)⦄) :
    ⦃P⦄ (x >>= f) ⦃Q⦄ := Triple.bind x f h (fun _ => .rfl)

@[spec]
theorem Specs.bind {m : Type → Type u} {ps : PostShape} [Monad m] [WPMonad m ps] {α β} {x : m α} {f : α → m β} {Q : PostCond β ps} :
  ⦃wp⟦x⟧ (fun a => wp⟦f a⟧ Q, Q.2)⦄ (x >>= f) ⦃Q⦄ := Specs.bind' .rfl

@[spec]
theorem Specs.map {m : Type → Type u} {ps : PostShape} [Monad m] [WPMonad m ps] {α β} {x : m α} {f : α → β} {Q : PostCond β ps} :
  ⦃wp⟦x⟧ (fun a => Q.1 (f a), Q.2)⦄ (f <$> x) ⦃Q⦄ := by simp only [Triple, WP.map_apply, SPred.entails.refl]

@[spec]
theorem Specs.seq {m : Type → Type u} {ps : PostShape} [Monad m] [WPMonad m ps] {α β} {x : m (α → β)} {y : m α} {Q : PostCond β ps} :
  ⦃wp⟦x⟧ (fun f => wp⟦y⟧ (fun a => Q.1 (f a), Q.2), Q.2)⦄ (x <*> y) ⦃Q⦄ := by simp only [Triple, WP.seq_apply, SPred.entails.refl]

/-! # `MonadLift` -/

@[spec]
theorem Specs.monadLift_StateT [Monad m] [WPMonad m ps] (x : m α) (Q : PostCond α (.arg σ ps)) :
  ⦃fun s => wp⟦x⟧ (fun a => Q.1 a s, Q.2)⦄ (MonadLift.monadLift x : StateT σ m α) ⦃Q⦄ := by simp only [Triple, StateT.monadLift_apply, SPred.entails.refl]

@[spec]
theorem Specs.monadLift_ReaderT [Monad m] [WPMonad m ps] (x : m α) (Q : PostCond α (.arg ρ ps)) :
  ⦃fun s => wp⟦x⟧ (fun a => Q.1 a s, Q.2)⦄ (MonadLift.monadLift x : ReaderT ρ m α) ⦃Q⦄ := by simp only [Triple, ReaderT.monadLift_apply, SPred.entails.refl]

@[spec]
theorem Specs.monadLift_ExceptT [Monad m] [WPMonad m ps] (x : m α) (Q : PostCond α (.except ε ps)) :
-- strange elab error; apparently tries hard to instantiate ps to ps instead of `.except ε ps`
--  ⦃(wp⟦x⟧ (fun a => Q.1 a, Q.2.2) : Assertion (.except ε ps))⦄ (MonadLift.monadLift x : ExceptT ε m α) ⦃Q⦄ := by simp only [Triple, ExceptT.monadLift_apply, SPred.entails.refl]
  Triple (ps:=.except ε ps) (MonadLift.monadLift x : ExceptT ε m α) (wp⟦x⟧ (fun a => Q.1 a, Q.2.2)) Q := by simp only [Triple, ExceptT.monadLift_apply, SPred.entails.refl]

/-! # `MonadLiftT` -/

@[spec]
theorem Specs.monadLift_trans [WP o ps] [MonadLift n o] [MonadLiftT m n] :
  ⦃wp⟦MonadLift.monadLift (m:=n) (MonadLiftT.monadLift (m:=m) x) : o α⟧ Q⦄ (MonadLiftT.monadLift x : o α) ⦃Q⦄ := by
    simp only [Triple, MonadLiftT.monadLift_trans_apply, SPred.entails.refl]

@[spec]
theorem Specs.monadLift_refl [WP m ps] :
  ⦃wp⟦x : m α⟧ Q⦄ (MonadLiftT.monadLift x : m α) ⦃Q⦄ := by
    simp only [Triple, MonadLiftT.monadLift_refl_apply, SPred.entails.refl]

/-! # `MonadFunctor` -/

@[spec]
theorem Specs.monadMap_StateT [Monad m] [WP m psm]
    (f : ∀{β}, m β → m β) {α} (x : StateT σ m α) (Q : PostCond α (.arg σ psm)) :
    ⦃fun s => wp⟦f (x.run s)⟧ (fun (a, s) => Q.1 a s, Q.2)⦄ (MonadFunctor.monadMap (m:=m) f x) ⦃Q⦄ := by
  simp only [Triple, StateT.monadMap_apply, SPred.entails.refl]

@[spec]
theorem Specs.monadMap_ReaderT [Monad m] [WP m psm]
    (f : ∀{β}, m β → m β) {α} (x : ReaderT ρ m α) (Q : PostCond α (.arg ρ psm)) :
    ⦃fun s => wp⟦f (x.run s)⟧ (fun a => Q.1 a s, Q.2)⦄ (MonadFunctor.monadMap (m:=m) f x) ⦃Q⦄ := by
  simp only [Triple, ReaderT.monadMap_apply, SPred.entails.refl]

@[spec]
theorem Specs.monadMap_ExceptT [Monad m] [WP m psm]
    (f : ∀{β}, m β → m β) {α} (x : ExceptT ε m α) (Q : PostCond α (.except ε psm)) :
    Triple (ps:=.except ε psm) (MonadFunctor.monadMap (m:=m) f x) (wp⟦f x.run⟧ (fun | .ok a => Q.1 a | .error e => Q.2.1 e, Q.2.2)) Q := by
  simp only [Triple, ExceptT.monadMap_apply, SPred.entails.refl]; rfl

/-! # `MonadFunctorT` -/

@[spec]
theorem Specs.monadMap_trans [WP o ps] [MonadFunctor n o] [MonadFunctorT m n] :
  ⦃wp⟦MonadFunctor.monadMap (m:=n) (MonadFunctorT.monadMap (m:=m) f) x : o α⟧ Q⦄
  (MonadFunctorT.monadMap f x : o α)
  ⦃Q⦄ := by simp only [Triple, MonadFunctorT.monadMap, SPred.entails.rfl]

@[spec]
theorem Specs.monadMap_refl [WP m ps] :
  ⦃wp⟦f x : m α⟧ Q⦄
  (MonadFunctorT.monadMap f x : m α)
  ⦃Q⦄ := by simp only [Triple, MonadFunctorT.monadMap, SPred.entails.rfl]

/-! # `ReaderT` -/

@[spec]
theorem Specs.run_ReaderT [WP m ps] (x : ReaderT ρ m α) :
  ⦃wp⟦x⟧ (fun a _ => Q.1 a, Q.2) r⦄ x.run r ⦃Q⦄ := by simp only [Triple, WP.ReaderT_run_apply, SPred.entails.rfl]

@[spec]
theorem Specs.read_ReaderT [Monad m] [WPMonad m psm] :
  ⦃fun r => Q.1 r r⦄ (MonadReaderOf.read : ReaderT ρ m ρ) ⦃Q⦄ := by simp only [Triple, ReaderT.read_apply, SPred.entails.rfl]

@[spec]
theorem Specs.withReader_ReaderT [Monad m] [WPMonad m psm] :
    ⦃fun r => wp⟦x⟧ (fun a _ => Q.1 a r, Q.2) (f r)⦄
    (MonadWithReaderOf.withReader f x : ReaderT ρ m α)
    ⦃Q⦄ := by
  simp only [Triple, ReaderT.withReader_apply, SPred.entails.rfl]

/-! # `StateT` -/

@[spec]
theorem Specs.run_StateT [WP m ps] (x : StateT σ m α) :
  ⦃wp⟦x⟧ (fun a s => Q.1 (a, s), Q.2) s⦄ x.run s ⦃Q⦄ := by simp only [Triple, WP.StateT_run_apply, SPred.entails.rfl]

@[spec]
theorem Specs.get_StateT [Monad m] [WPMonad m psm] :
  ⦃fun s => Q.1 s s⦄ (MonadStateOf.get : StateT σ m σ) ⦃Q⦄ := by simp only [Triple, StateT.get_apply, SPred.entails.rfl]

@[spec]
theorem Specs.set_StateT [Monad m] [WPMonad m psm] :
  ⦃fun _ => Q.1 () s⦄ (MonadStateOf.set s : StateT σ m PUnit) ⦃Q⦄ := by simp only [Triple, StateT.set_apply, SPred.entails.rfl]

@[spec]
theorem Specs.modifyGet_StateT [Monad m] [WPMonad m ps] :
  ⦃fun s => Q.1 (f s).1 (f s).2⦄ (MonadStateOf.modifyGet f : StateT σ m α) ⦃Q⦄ := by
    simp only [Triple, StateT.modifyGet_apply, SPred.entails.rfl]

/-! # `ExceptT` -/

@[spec]
theorem Specs.run_ExceptT [WP m ps] (x : ExceptT ε m α) :
    Triple (ps:=ps) x.run (wp⟦x⟧ (fun a => Q.1 (.ok a), fun e => Q.1 (.error e), Q.2)) Q := by
  simp only [Triple, WP.ExceptT_run_apply, SPred.entails.rfl]

@[spec]
theorem Specs.throw_ExceptT [Monad m] [WPMonad m ps] :
    ⦃Q.2.1 e⦄ (MonadExceptOf.throw e : ExceptT ε m α) ⦃Q⦄ := by
  simp only [Triple, ExceptT.throw_apply, SPred.entails.rfl]

@[spec]
theorem Specs.tryCatch_ExceptT [Monad m] [WPMonad m ps] (Q : PostCond α (.except ε ps)) :
    ⦃wp⟦x⟧ (Q.1, fun e => wp⟦h e⟧ Q, Q.2.2)⦄ (MonadExceptOf.tryCatch x h : ExceptT ε m α) ⦃Q⦄ := by
  simp only [Triple, ExceptT.tryCatch_apply, SPred.entails.rfl]

/-! # `Except` -/

@[spec]
theorem Specs.throw_Except [Monad m] [WPMonad m ps] :
    ⦃Q.2.1 e⦄ (MonadExceptOf.throw e : Except ε α) ⦃Q⦄ := SPred.entails.rfl

@[spec]
theorem Specs.tryCatch_Except (Q : PostCond α (.except ε .pure)) :
    ⦃wp⟦x⟧ (Q.1, fun e => wp⟦h e⟧ Q, Q.2.2)⦄ (MonadExceptOf.tryCatch x h : Except ε α) ⦃Q⦄ := by
  simp only [Triple, Except.tryCatch_apply, SPred.entails.rfl]

/-! # `EStateM` -/

@[spec]
theorem Specs.get_EStateM [Monad m] [WPMonad m psm] :
  ⦃fun s => Q.1 s s⦄ (MonadStateOf.get : EStateM ε σ σ) ⦃Q⦄ := SPred.entails.rfl

@[spec]
theorem Specs.set_EStateM [Monad m] [WPMonad m psm] :
  ⦃fun _ => Q.1 () s⦄ (MonadStateOf.set s : EStateM ε σ PUnit) ⦃Q⦄ := SPred.entails.rfl

@[spec]
theorem Specs.modifyGet_EStateM [Monad m] [WPMonad m psm] :
    ⦃fun s => Q.1 (f s).1 (f s).2⦄ (MonadStateOf.modifyGet f : EStateM ε σ α) ⦃Q⦄ := SPred.entails.rfl

@[spec]
theorem Specs.throw_EStateM [Monad m] [WPMonad m psm] :
    ⦃Q.2.1 e⦄ (MonadExceptOf.throw e : EStateM ε σ α) ⦃Q⦄ := SPred.entails.rfl

open EStateM.Backtrackable in
@[spec]
theorem Specs.tryCatch_EStateM (Q : PostCond α (.except ε (.arg σ .pure))) :
    ⦃fun s => wp⟦x⟧ (Q.1, fun e s' => wp⟦h e⟧ Q (restore s' (save s)), Q.2.2) s⦄ (MonadExceptOf.tryCatch x h : EStateM ε σ α) ⦃Q⦄ := by
  simp only [Triple, EStateM.tryCatch_apply, SPred.entails.rfl]

/-! # Lifting `MonadStateOf` -/

@[spec]
theorem Specs.get_MonadStateOf [MonadStateOf σ m] [MonadLift m n] [WP n _]:
    ⦃wp⟦MonadLift.monadLift (MonadStateOf.get : m σ) : n σ⟧ Q⦄
    (MonadStateOf.get : n σ)
    ⦃Q⦄ := SPred.entails.rfl

@[spec]
theorem Specs.getThe_MonadStateOf [MonadStateOf σ m] [MonadLift m n] [WP n _]:
    ⦃wp⟦MonadLift.monadLift (MonadStateOf.get : m σ) : n σ⟧ Q⦄
    (getThe σ : n σ)
    ⦃Q⦄ := Specs.get_MonadStateOf

@[spec]
theorem Specs.get_MonadState [MonadStateOf σ m] [MonadLift m n] [WP n _]:
    ⦃wp⟦MonadLift.monadLift (MonadStateOf.get : m σ) : n σ⟧ Q⦄
    (MonadState.get : n σ)
    ⦃Q⦄ := Specs.get_MonadStateOf

@[spec]
theorem Specs.set_MonadStateOf [MonadStateOf σ m] [MonadLift m n] [WP n _]:
    ⦃wp⟦MonadLift.monadLift (MonadStateOf.set (σ:=σ) s : m PUnit) : n PUnit⟧ Q⦄
    (MonadStateOf.set s : n PUnit)
    ⦃Q⦄ := SPred.entails.rfl

@[spec]
theorem Specs.set_MonadState [MonadStateOf σ m] [MonadLift m n] [WP n _]:
    ⦃wp⟦MonadLift.monadLift (MonadStateOf.set (σ:=σ) s : m PUnit) : n PUnit⟧ Q⦄
    (MonadState.set s : n PUnit)
    ⦃Q⦄ := SPred.entails.rfl

@[spec]
theorem Specs.modifyGet_MonadStateOf [MonadStateOf σ m] [MonadLift m n] [WP n _]:
    ⦃wp⟦MonadLift.monadLift (MonadStateOf.modifyGet (σ:=σ) f : m α) : n α⟧ Q⦄
    (MonadStateOf.modifyGet f : n α)
    ⦃Q⦄ := SPred.entails.rfl

@[spec]
theorem Specs.modifyGet_MonadState [MonadStateOf σ m] [MonadLift m n] [WP n _]:
    ⦃wp⟦MonadLift.monadLift (MonadStateOf.modifyGet (σ:=σ) f : m α) : n α⟧ Q⦄
    (MonadState.modifyGet f : n α)
    ⦃Q⦄ := SPred.entails.rfl

@[spec]
theorem Specs.modify_MonadStateOf [MonadStateOf σ m] [MonadLift m n] [WP n _]:
    ⦃wp⟦MonadLift.monadLift (MonadStateOf.modifyGet fun s => ((), f s) : m PUnit) : n PUnit⟧ Q⦄
    (modify f : n PUnit)
    ⦃Q⦄ := SPred.entails.rfl

@[spec]
theorem Specs.modify_MonadState [MonadStateOf σ m] [MonadLift m n] [WP n _]:
    ⦃wp⟦MonadLift.monadLift (MonadStateOf.modifyGet fun s => ((), f s) : m PUnit) : n PUnit⟧ Q⦄
    (modifyThe σ f : n PUnit)
    ⦃Q⦄ := SPred.entails.rfl

/-! # Lifting `MonadReaderOf` -/

@[spec]
theorem Specs.read_MonadReaderOf [MonadReaderOf ρ m] [MonadLift m n] [WP n _]:
    ⦃wp⟦MonadLift.monadLift (MonadReaderOf.read : m ρ) : n ρ⟧ Q⦄
    (MonadReaderOf.read : n ρ)
    ⦃Q⦄ := SPred.entails.rfl

@[spec]
theorem Specs.readThe_MonadReaderOf [MonadReaderOf ρ m] [MonadLift m n] [WP n _]:
    ⦃wp⟦MonadLift.monadLift (MonadReaderOf.read : m ρ) : n ρ⟧ Q⦄
    (readThe ρ : n ρ)
    ⦃Q⦄ := Specs.read_MonadReaderOf

@[spec]
theorem Specs.read_MonadReader [MonadReaderOf ρ m] [MonadLift m n] [WP n _]:
    ⦃wp⟦MonadLift.monadLift (MonadReaderOf.read : m ρ) : n ρ⟧ Q⦄
    (MonadReader.read : n ρ)
    ⦃Q⦄ := Specs.read_MonadReaderOf

@[spec]
theorem Specs.withReader_MonadReaderOf [MonadWithReaderOf ρ m] [MonadFunctor m n] [WP n _] (f : ρ → ρ) (x : n α) :
    ⦃wp⟦MonadFunctor.monadMap (m:=m) (MonadWithReaderOf.withReader f) x : n α⟧ Q⦄
    (MonadWithReaderOf.withReader f x : n α)
    ⦃Q⦄ := SPred.entails.rfl

@[spec]
theorem Specs.withTheReader_MonadReaderOf [MonadWithReaderOf ρ m] [MonadFunctor m n] [WP n _] (f : ρ → ρ) (x : n α) :
    ⦃wp⟦MonadFunctor.monadMap (m:=m) (MonadWithReaderOf.withReader f) x : n α⟧ Q⦄
    (withTheReader ρ f x : n α)
    ⦃Q⦄ := SPred.entails.rfl

@[spec]
theorem Specs.withReader_MonadReader [MonadWithReaderOf ρ m] [MonadFunctor m n] [WP n _] (f : ρ → ρ) (x : n α) :
    ⦃wp⟦MonadFunctor.monadMap (m:=m) (MonadWithReaderOf.withReader f) x : n α⟧ Q⦄
    (MonadWithReader.withReader f x : n α)
    ⦃Q⦄ := SPred.entails.rfl

/-! # Lifting `MonadExceptOf` -/

@[spec]
theorem Specs.throw_MonadExcept [MonadExceptOf ε m] [WP m _]:
    ⦃wp⟦MonadExceptOf.throw e : m α⟧ Q⦄
    (throw e : m α)
    ⦃Q⦄ := SPred.entails.rfl

@[spec]
theorem Specs.throwThe_MonadExcept [MonadExceptOf ε m] [WP m _]:
    ⦃wp⟦MonadExceptOf.throw e : m α⟧ Q⦄
    (throwThe ε e : m α)
    ⦃Q⦄ := SPred.entails.rfl

@[spec]
theorem Specs.tryCatch_MonadExcept [MonadExceptOf ε m] [WP m ps] (Q : PostCond α ps) :
    ⦃wp⟦MonadExceptOf.tryCatch x h : m α⟧ Q⦄
    (tryCatch x h : m α)
    ⦃Q⦄ := SPred.entails.rfl

@[spec]
theorem Specs.tryCatchThe_MonadExcept [MonadExceptOf ε m] [WP m ps] (Q : PostCond α ps) :
    ⦃wp⟦MonadExceptOf.tryCatch x h : m α⟧ Q⦄
    (tryCatchThe ε x h : m α)
    ⦃Q⦄ := SPred.entails.rfl

@[spec]
theorem Specs.throw_ReaderT  [WP m sh] [Monad m] [MonadExceptOf ε m] :
    ⦃wp⟦MonadLift.monadLift (MonadExceptOf.throw (ε:=ε) e : m α) : ReaderT ρ m α⟧ Q⦄
    (MonadExceptOf.throw e : ReaderT ρ m α)
    ⦃Q⦄ := SPred.entails.rfl

@[spec]
theorem Specs.throw_StateT [WP m ps] [Monad m] [MonadExceptOf ε m] (Q : PostCond α (.arg σ ps)) :
    ⦃wp⟦MonadLift.monadLift (MonadExceptOf.throw (ε:=ε) e : m α) : StateT σ m α⟧ Q⦄
    (MonadExceptOf.throw e : StateT σ m α)
    ⦃Q⦄ := SPred.entails.rfl

@[spec]
theorem Specs.throw_ExceptT_lift [WP m ps] [Monad m] [MonadExceptOf ε m] (Q : PostCond α (.except ε' ps)) :
    Triple
      (ps:=.except ε' ps)
      (MonadExceptOf.throw e : ExceptT ε' m α)
      (wp⟦MonadExceptOf.throw (ε:=ε) e : m (Except ε' α)⟧ (fun | .ok a => Q.1 a | .error e => Q.2.1 e, Q.2.2))
      Q := by
  simp only [Triple, ExceptT.lift_throw_apply, SPred.entails.rfl]
  apply (wp _).mono
  simp
  intro x
  split <;> rfl

@[spec]
theorem Specs.tryCatch_ReaderT [WP m ps] [Monad m] [MonadExceptOf ε m] (Q : PostCond α (.arg ρ ps)) :
    ⦃fun r => wp⟦MonadExceptOf.tryCatch (ε:=ε) (x.run r) (fun e => (h e).run r) : m α⟧ (fun a => Q.1 a r, Q.2)⦄
    (MonadExceptOf.tryCatch x h : ReaderT ρ m α)
    ⦃Q⦄ := SPred.entails.rfl

@[spec]
theorem Specs.tryCatch_StateT [WP m ps] [Monad m] [MonadExceptOf ε m] (Q : PostCond α (.arg σ ps)) :
    ⦃fun s => wp⟦MonadExceptOf.tryCatch (ε:=ε) (x.run s) (fun e => (h e).run s) : m (α × σ)⟧ (fun as => Q.1 as.1 as.2, Q.2)⦄
    (MonadExceptOf.tryCatch x h : StateT σ m α)
    ⦃Q⦄ := SPred.entails.rfl

@[spec]
theorem Specs.tryCatch_ExceptT_lift [WP m ps] [Monad m] [MonadExceptOf ε m] (Q : PostCond α (.except ε' ps)) :
    Triple
      (ps:=.except ε' ps)
      (MonadExceptOf.tryCatch x h : ExceptT ε' m α)
      (wp⟦MonadExceptOf.tryCatch (ε:=ε) x h : m (Except ε' α)⟧ (fun | .ok a => Q.1 a | .error e => Q.2.1 e, Q.2.2))
      Q := by
  simp only [Triple, ExceptT.lift_tryCatch_apply, SPred.entails.rfl]
  apply (wp _).mono
  simp
  intro x
  split <;> rfl

/-! # `ForIn` -/

@[spec]
theorem Specs.forIn'_list {α : Type} {β : Type} {m : Type → Type v} {ps : PostShape}
    [Monad m] [WPMonad m ps]
    {xs : List α} {init : β} {f : (a : α) → a ∈ xs → β → m (ForInStep β)}
    (inv : PostCond (β × List.Zipper xs) ps)
    (step : ∀ b rpref x (hx : x ∈ xs) suff (h : xs = rpref.reverse ++ x :: suff),
        ⦃inv.1 (b, ⟨rpref, x::suff, by simp [h]⟩)⦄
        f x hx b
        ⦃(fun r => match r with
                   | .yield b' => inv.1 (b', ⟨x::rpref, suff, by simp [h]⟩)
                   | .done b' => inv.1 (b', ⟨xs.reverse, [], by simp⟩), inv.2)⦄) :
    ⦃inv.1 (init, ⟨[], xs, by simp⟩)⦄ forIn' xs init f ⦃(fun b => inv.1 (b, ⟨xs.reverse, [], by simp⟩), inv.2)⦄ := by
  suffices h : ∀ rpref suff (h : xs = rpref.reverse ++ suff),
      ⦃inv.1 (init, ⟨rpref, suff, by simp [h]⟩)⦄
      forIn' (m:=m) suff init (fun a ha => f a (by simp[h,ha]))
      ⦃(fun b => inv.1 (b, ⟨xs.reverse, [], by simp [h]⟩), inv.2)⦄
    from h [] xs rfl
  intro rpref suff h
  induction suff generalizing rpref init
  case nil => apply Triple.pure; simp [h]
  case cons x suff ih =>
    simp only [List.forIn'_cons]
    apply Triple.bind
    case hx => exact step init rpref x (by simp[h]) suff h
    case hf =>
      intro r
      split
      next => apply Triple.pure; simp [h]
      next b =>
        simp
        have := @ih b (x::rpref) (by simp [h])
        simp at this
        exact this

-- using the postcondition as a constant invariant:
theorem Specs.forIn'_list_const_inv {α : Type} {β : Type} {m : Type → Type v} {ps : PostShape}
  [Monad m] [WPMonad m ps]
  {xs : List α} {init : β} {f : (a : α) → a ∈ xs → β → m (ForInStep β)}
  {inv : PostCond β ps}
  (step : ∀ x (hx : x ∈ xs) b,
      ⦃inv.1 b⦄
      f x hx b
      ⦃(fun r => match r with | .yield b' => inv.1 b' | .done b' => inv.1 b', inv.2)⦄) :
  ⦃inv.1 init⦄ forIn' xs init f ⦃inv⦄ :=
    Specs.forIn'_list (fun p => inv.1 p.1, inv.2) (fun b _ x hx _ _ => step x hx b)

@[spec]
theorem Specs.forIn_list {α : Type} {β : Type} {m : Type → Type v} {ps : PostShape}
    [Monad m] [WPMonad m ps]
    {xs : List α} {init : β} {f : α → β → m (ForInStep β)}
    (inv : PostCond (β × List.Zipper xs) ps)
    (step : ∀ b rpref x suff (h : xs = rpref.reverse ++ x :: suff),
        ⦃inv.1 (b, ⟨rpref, x::suff, by simp [h]⟩)⦄
        f x b
        ⦃(fun r => match r with
                   | .yield b' => inv.1 (b', ⟨x::rpref, suff, by simp [h]⟩)
                   | .done b' => inv.1 (b', ⟨xs.reverse, [], by simp⟩), inv.2)⦄) :
    ⦃inv.1 (init, ⟨[], xs, by simp⟩)⦄ forIn xs init f ⦃(fun b => inv.1 (b, ⟨xs.reverse, [], by simp⟩), inv.2)⦄ := by
  simp only [← forIn'_eq_forIn]
  exact Specs.forIn'_list inv (fun b rpref x _ suff h => step b rpref x suff h)

-- using the postcondition as a constant invariant:
theorem Specs.forIn_list_const_inv {α : Type} {β : Type} {m : Type → Type v} {ps : PostShape}
  [Monad m] [WPMonad m ps]
  {xs : List α} {init : β} {f : α → β → m (ForInStep β)}
  {inv : PostCond β ps}
  (step : ∀ hd b,
      ⦃inv.1 b⦄
      f hd b
      ⦃(fun r => match r with | .yield b' => inv.1 b' | .done b' => inv.1 b', inv.2)⦄) :
  ⦃inv.1 init⦄ forIn xs init f ⦃inv⦄ :=
    Specs.forIn_list (fun p => inv.1 p.1, inv.2) (fun b _ hd _ _ => step hd b)

@[spec]
theorem Specs.foldlM_list {α : Type} {β : Type} {m : Type → Type v} {ps : PostShape}
  [Monad m] [WPMonad m ps]
  {xs : List α} {init : β} {f : β → α → m β}
  (inv : PostCond (β × List.Zipper xs) ps)
  (step : ∀ b rpref x suff (h : xs = rpref.reverse ++ x :: suff),
      ⦃inv.1 (b, ⟨rpref, x::suff, by simp [h]⟩)⦄
      f b x
      ⦃(fun b' => inv.1 (b', ⟨x::rpref, suff, by simp [h]⟩), inv.2)⦄) :
  ⦃inv.1 (init, ⟨[], xs, by simp⟩)⦄ List.foldlM f init xs ⦃(fun b => inv.1 (b, ⟨xs.reverse, [], by simp⟩), inv.2)⦄ := by
  have : xs.foldlM f init = forIn xs init (fun a b => .yield <$> f b a) := by
    simp only [List.forIn_yield_eq_foldlM, id_map']
  rw[this]
  apply Specs.forIn_list inv
  simp only [Triple, map_map, PredTrans.map_apply]
  exact step

-- using the postcondition as a constant invariant:
theorem Specs.foldlM_list_const_inv {α : Type} {β : Type} {m : Type → Type v} {ps : PostShape}
  [Monad m] [WPMonad m ps]
  {xs : List α} {init : β} {f : β → α → m β}
  {inv : PostCond β ps}
  (step : ∀ hd b,
      ⦃inv.1 b⦄
      f b hd
      ⦃(fun b' => inv.1 b', inv.2)⦄) :
  ⦃inv.1 init⦄ List.foldlM f init xs ⦃inv⦄ :=
    Specs.foldlM_list (fun p => inv.1 p.1, inv.2) (fun b _ hd _ _ => step hd b)

@[spec]
theorem Specs.forIn'_range {β : Type} {m : Type → Type v} {ps : PostShape}
    [Monad m] [WPMonad m ps]
    {xs : Std.Range} {init : β} {f : (a : Nat) → a ∈ xs → β → m (ForInStep β)}
    (inv : PostCond (β × List.Zipper xs.toList) ps)
    (step : ∀ b rpref x (hx : x ∈ xs) suff (h : xs.toList = rpref.reverse ++ x :: suff),
        ⦃inv.1 (b, ⟨rpref, x::suff, by simp [h]⟩)⦄
        f x hx b
        ⦃(fun r => match r with
                   | .yield b' => inv.1 (b', ⟨x::rpref, suff, by simp [h]⟩)
                   | .done b' => inv.1 (b', ⟨xs.toList.reverse, [], by simp⟩), inv.2)⦄) :
    ⦃inv.1 (init, ⟨[], xs.toList, by simp⟩)⦄ forIn' xs init f ⦃(fun b => inv.1 (b, ⟨xs.toList.reverse, [], by simp⟩), inv.2)⦄ := by
  simp only [Std.Range.forIn'_eq_forIn'_range', Std.Range.size, Std.Range.size.eq_1]
  apply Specs.forIn'_list inv (fun b rpref x hx suff h => step b rpref x (Std.Range.mem_of_mem_range' hx) suff h)

@[spec]
theorem Specs.forIn_range {β : Type} {m : Type → Type v} {ps : PostShape}
    [Monad m] [WPMonad m ps]
    {xs : Std.Range} {init : β} {f : Nat → β → m (ForInStep β)}
    (inv : PostCond (β × List.Zipper xs.toList) ps)
    (step : ∀ b rpref x suff (h : xs.toList = rpref.reverse ++ x :: suff),
        ⦃inv.1 (b, ⟨rpref, x::suff, by simp [h]⟩)⦄
        f x b
        ⦃(fun r => match r with
                   | .yield b' => inv.1 (b', ⟨x::rpref, suff, by simp [h]⟩)
                   | .done b' => inv.1 (b', ⟨xs.toList.reverse, [], by simp⟩), inv.2)⦄) :
    ⦃inv.1 (init, ⟨[], xs.toList, by simp⟩)⦄ forIn xs init f ⦃(fun b => inv.1 (b, ⟨xs.toList.reverse, [], by simp⟩), inv.2)⦄ := by
  simp only [Std.Range.forIn_eq_forIn_range', Std.Range.size]
  apply Specs.forIn_list inv step

@[spec]
theorem Specs.forIn'_array {α : Type} {β : Type} {m : Type → Type v} {ps : PostShape}
    [Monad m] [WPMonad m ps]
    {xs : Array α} {init : β} {f : (a : α) → a ∈ xs → β → m (ForInStep β)}
    (inv : PostCond (β × List.Zipper xs.toList) ps)
    (step : ∀ b rpref x (hx : x ∈ xs) suff (h : xs.toList = rpref.reverse ++ x :: suff),
        ⦃inv.1 (b, ⟨rpref, x::suff, by simp [h]⟩)⦄
        f x hx b
        ⦃(fun r => match r with
                   | .yield b' => inv.1 (b', ⟨x::rpref, suff, by simp [h]⟩)
                   | .done b' => inv.1 (b', ⟨xs.toList.reverse, [], by simp⟩), inv.2)⦄) :
    ⦃inv.1 (init, ⟨[], xs.toList, by simp⟩)⦄ forIn' xs init f ⦃(fun b => inv.1 (b, ⟨xs.toList.reverse, [], by simp⟩), inv.2)⦄ := by
  cases xs
  simp
  apply Specs.forIn'_list inv (fun b rpref x hx suff h => step b rpref x (by simp[hx]) suff h)

@[spec]
theorem Specs.forIn_array {α : Type} {β : Type} {m : Type → Type v} {ps : PostShape}
    [Monad m] [WPMonad m ps]
    {xs : Array α} {init : β} {f : α → β → m (ForInStep β)}
    (inv : PostCond (β × List.Zipper xs.toList) ps)
    (step : ∀ b rpref x suff (h : xs.toList = rpref.reverse ++ x :: suff),
        ⦃inv.1 (b, ⟨rpref, x::suff, by simp [h]⟩)⦄
        f x b
        ⦃(fun r => match r with
                   | .yield b' => inv.1 (b', ⟨x::rpref, suff, by simp [h]⟩)
                   | .done b' => inv.1 (b', ⟨xs.toList.reverse, [], by simp⟩), inv.2)⦄) :
    ⦃inv.1 (init, ⟨[], xs.toList, by simp⟩)⦄ forIn xs init f ⦃(fun b => inv.1 (b, ⟨xs.toList.reverse, [], by simp⟩), inv.2)⦄ := by
  cases xs
  simp
  apply Specs.forIn_list inv step

@[spec]
theorem Specs.foldlM_array {α : Type} {β : Type} {m : Type → Type v} {ps : PostShape}
  [Monad m] [WPMonad m ps]
  {xs : Array α} {init : β} {f : β → α → m β}
  (inv : PostCond (β × List.Zipper xs.toList) ps)
  (step : ∀ b rpref x suff (h : xs.toList = rpref.reverse ++ x :: suff),
      ⦃inv.1 (b, ⟨rpref, x::suff, by simp [h]⟩)⦄
      f b x
      ⦃(fun b' => inv.1 (b', ⟨x::rpref, suff, by simp [h]⟩), inv.2)⦄) :
  ⦃inv.1 (init, ⟨[], xs.toList, by simp⟩)⦄ Array.foldlM f init xs ⦃(fun b => inv.1 (b, ⟨xs.toList.reverse, [], by simp⟩), inv.2)⦄ := by
  cases xs
  simp
  apply Specs.foldlM_list inv step

end MPL
