import MPL.WPMonad
import MPL.WPMonadLift

namespace MPL

universe u
variable {m : Type → Type u} {ps : PredShape}

protected theorem ReaderT.wp_withReader [WP m psm] :
  wp⟦MonadWithReaderOf.withReader f x : ReaderT ρ m α⟧ = PredTrans.withReader f wp⟦x⟧ := rfl

theorem ReaderT.withReader_apply [WP m psm] :
  wp⟦MonadWithReaderOf.withReader f x : ReaderT ρ m α⟧.apply Q = fun r => wp⟦x⟧.apply (fun a _ => Q.1 a r, Q.2) (f r) := by
    simp only [ReaderT.wp_withReader, PredTrans.withReader_apply]

theorem MonadWithReaderOf.withReader_apply [MonadWithReaderOf ρ m] [WP m msh] [WP n nsh] [MonadFunctor m n] [MonadFunctor (PredTrans msh) (PredTrans nsh)] (f : ρ → ρ) (x : n α) :
  wp⟦MonadWithReaderOf.withReader f x⟧.apply Q = wp⟦MonadFunctor.monadMap (m:=m) (MonadWithReaderOf.withReader f) x⟧.apply Q := rfl

theorem MonadWithReaderOf.withTheReader_apply [MonadWithReaderOf ρ m] [WP m sh] (f : ρ → ρ) (x : m α) :
  wp⟦withTheReader ρ f x⟧.apply Q = wp⟦MonadWithReaderOf.withReader f x⟧.apply Q := rfl

theorem MonadWithReader.withReader_apply [MonadWithReaderOf ρ m] [WP m sh] (f : ρ → ρ) (x : m α) :
  wp⟦MonadWithReader.withReader f x⟧.apply Q = wp⟦MonadWithReaderOf.withReader f x⟧.apply Q := rfl

-- Dependency analysis:
-- * To express monadMap_apply, we need wp1
-- * To reduce wp1 applications, we need WP.wp1_apply
-- * WP.wp1_apply needs ParametricNT.wp_app
-- * ReaderT.instWPMonadFunctor needs ParametricNT.wp_map_map

open MonadFunctor renaming monadMap → mmap

-- wp is a representation function. We get a Galois Connection
--   α(X) := ⨆{ wp⟦x⟧ | x ∈ X }
--   γ(t) := { x | wp⟦x⟧ ≤ t }
--   α(f)(t) := ⨆{ wp⟦f x⟧ | wp⟦x⟧ ≤ t }
-- wp1⟦f⟧ is exactly α(f).
noncomputable def wp1 {m : Type → Type u} {ps : PredShape} [WP m ps] (f : ∀{α}, m α → m α) {α} : PredTrans ps α → PredTrans ps α := fun t =>
  sSup { r | ∃ x, wp⟦x⟧ ≤ t ∧ r = wp⟦f x⟧ }

-- The following type class expresses that any function of type
-- (f : ∀{α}, m α → m α) is parametric; that is,
-- (1) preserves relations such as `wp⟦·⟧ ≤ wp⟦·⟧`, and
-- (2) is a natural transformation. (At least (2) is folklore.)
class ParametricNT (m : Type → Type u) (ps : outParam PredShape) [WP m ps] [Monad m] (f : ∀{α}, m α → m α) where
  wp_app : ∀ {α} (x x' : m α), wp⟦x⟧ ≤ wp⟦x'⟧ → wp⟦f x⟧ ≤ wp⟦f x'⟧
  wp_map_map : ∀ {α} (g : α → β) (x : m α), f (g <$> x) = g <$> f x

instance ReaderT.instParametricNTWithReader {m : Type → Type} {ps : PredShape} [WP m ps] [Monad m] (f : ρ → ρ) : ParametricNT (ReaderT ρ m) (.arg ρ ps) (MonadWithReaderOf.withReader f) where
  wp_app x x' h := by simp only [ReaderT.wp_withReader]; apply PredTrans.withReader_mono f _ _ h
  wp_map_map g x := by simp only [MonadFunctor.monadMap, Functor.map, ParametricNT.wp_map_map, MonadWithReaderOf.withReader]

instance MonadWithReaderOf.instParametricNTWithTheReader {m : Type → Type} (f : ρ → ρ) [MonadWithReaderOf ρ m] {ps : PredShape} [WP m ps] [Monad m] [base : ParametricNT m ps (MonadWithReaderOf.withReader f)] : ParametricNT m ps (withTheReader ρ f) where
  wp_app x x' h := by unfold withTheReader; apply ParametricNT.wp_app _ _ h
  wp_map_map g x := by unfold withTheReader; apply ParametricNT.wp_map_map g x

instance ReaderT.instParametricNT [WP m ps] (f : ∀{β}, m β → m β) [Monad m] [base : ParametricNT m ps f] : ParametricNT (ReaderT ρ m) (.arg ρ ps) (mmap (m:=m) f) where
  wp_app x x' h := by
    intro Q r
    apply base.wp_app
    intro Q
    apply h (fun a _ => Q.1 a, Q.2)
  wp_map_map g x := by simp only [MonadFunctor.monadMap, Functor.map, ParametricNT.wp_map_map]

instance StateT.instParametricNT [WP m ps] (f : ∀{β}, m β → m β) [Monad m] [LawfulMonad m] [base : ParametricNT m ps f] : ParametricNT (StateT σ m) (.arg σ ps) (mmap (m:=m) f) where
  wp_app x x' h := by
    intro Q s
    apply base.wp_app
    intro Q
    apply h (fun a s => Q.1 (a, s), Q.2)
  wp_map_map g x := by ext; simp only [StateT.run, MonadFunctor.monadMap, Functor.map, StateT.map,
    bind_pure_comp, ParametricNT.wp_map_map]

lemma except_eta {r : Sort u} (Q : Except ε α → r) : (fun | Except.ok a => Q (Except.ok a) | Except.error e => Q (Except.error e)) = Q := by
  ext x; cases x <;> rfl

instance ExceptT.instParametricNT [WP m ps] (f : ∀{β}, m β → m β) [Monad m] [LawfulMonad m] [base : ParametricNT m ps f] : ParametricNT (ExceptT ε m) (.except ε ps) (mmap (m:=m) f) where
  wp_app {α} x x' h := by
    intro Q
    apply base.wp_app
    intro Q
    replace h := h (fun a => Q.1 (.ok a), fun e => Q.1 (.error e), Q.2)
    simp only [wp, PredTrans.pushExcept] at h
    have heta : Q = (fun x => match x with | Except.ok a => Q.1 (Except.ok a) | Except.error e => Q.1 (Except.error e), Q.2) := by
      (ext x; cases x) <;> rfl
    apply le_trans _ (le_trans h _)
    · conv => lhs; rw [heta]
      sorry -- apply le_rfl -- Sigh. need to prove that LE (PreCond (.except ε ps)) = LE (PreCond ps)
    · conv => rhs; rw [heta]
      sorry -- apply le_rfl -- Sigh. need to prove that LE (PreCond (.except ε ps)) = LE (PreCond ps)
  wp_map_map g x := by
    -- F*CK ETA
    simp [ExceptT.run, MonadFunctor.monadMap, Functor.map, ExceptT.map, bind_pure_comp, ParametricNT.wp_map_map, ExceptT.mk]
    calc (f do let a ← x; match a with | Except.ok a => pure (Except.ok (g a)) | Except.error e => pure (Except.error e))
      _ = f (do let a ← x; pure (match a with | Except.ok a => .ok (g a) | Except.error e => .error e)) := by congr; ext; split <;> rfl
      _ = f ((fun a => (match a with | Except.ok a => .ok (g a) | Except.error e => .error e)) <$> x.run) := by simp only [bind_pure_comp, ExceptT.run]
      _ = (fun a => (match a with | Except.ok a => .ok (g a) | Except.error e => .error e)) <$> f x.run := by simp only [ParametricNT.wp_map_map]
      _ = (do let a ← f x; pure (match a with | Except.ok a => (Except.ok (g a)) | Except.error e => (Except.error e))) := by simp only [ExceptT.run, ←bind_pure_comp]
      _ = (do let a ← f x; match a with | Except.ok a => pure (Except.ok (g a)) | Except.error e => pure (Except.error e)) := by congr; ext; split <;> rfl

theorem WP.wp1_apply {m : Type → Type u} {ps : PredShape} [WP m ps] (f : ∀{α}, m α → m α) [Monad m] [ParametricNT m ps f] (x : m α) :
  wp1 (m:=m) f wp⟦x⟧ = wp⟦f x⟧ := by
    apply le_antisymm
    · apply sSup_le
      intro r ⟨x, hwpx, hwr⟩
      subst hwr
      apply ParametricNT.wp_app
      trivial
    · apply le_sSup
      use x, le_rfl

theorem ReaderT.wp_withReader2 [WP m psm] (f : ρ → ρ) {α} :
  wp1 (α:=α) (m := ReaderT ρ m) (MonadWithReaderOf.withReader f) ≤ PredTrans.withReader f := by
    intro t
    apply sSup_le
    intro r ⟨x, hwpx, hwr⟩
    subst hwr
    simp only [ReaderT.wp_withReader]
    apply PredTrans.withReader_mono
    trivial

example [WP m psm] (f : ρ → ρ) {α} :
  wp1 (α:=α) (m := ReaderT ρ m) (MonadWithReaderOf.withReader f) ≥ PredTrans.withReader f := by
    intro t
    match Classical.exists_or_forall_not (fun (x : ReaderT ρ m α) => wp⟦x⟧ ≤ t) with
    | .inl ⟨x, h⟩ => apply le_sSup; use x, h; sorry -- close enough?! but not really
    | .inr h => sorry -- no chance. The RHS is ⊥, but cannot show that t is bottom from h. Or can we?

class WPMonadFunctor (m : Type → Type u) (n : Type → Type v) [Monad m] [WP m psm] [WP n psn] [MonadFunctor m n] [MonadFunctor (PredTrans psm) (PredTrans psn)] where
  monadMap_apply (f : ∀{β}, m β → m β) [ParametricNT m psm f] {α} (x : n α) (Q : PostCond α psn) :
    wp⟦mmap (m:=m) f x⟧.apply Q = PredTrans.apply (mmap (m:=PredTrans psm) (wp1 (m:=m) f) wp⟦x⟧) Q
namespace WP
export WPMonadFunctor (monadMap_apply)
end WP

instance StateT.instWPMonadFunctor [WP m ps] [Monad m] : WPMonadFunctor m (StateT σ m)  where
  monadMap_apply f x _ := by
    simp only [wp, MonadFunctor.monadMap, PredTrans.popArg_pushArg, WP.wp1_apply, implies_true]

instance ReaderT.instWPMonadFunctor [WP m ps] [Monad m] [LawfulMonad m] [WPMonad m ps] : WPMonadFunctor m (ReaderT ρ m)  where
  monadMap_apply f base _ x := by
    simp only [wp, MonadFunctor.monadMap, PredTrans.popArg_pushArg, WP.wp1_apply, ←map_map, ParametricNT.wp_map_map, implies_true]

instance ExceptT.instWPMonadFunctor [WP m ps] [Monad m] [LawfulMonad m] [WPMonad m ps] : WPMonadFunctor m (ExceptT ε m) where
  monadMap_apply f x := by
    simp only [wp, MonadFunctor.monadMap, PredTrans.popExcept_pushExcept, WP.wp1_apply, implies_true]

-- Not presently needed. (? What would it be needed for?) If needed in the future, we need to resurrect monadMap_mono
/-
instance WPMonadFunctor.instParametricNT {m n : Type → Type} {psm psn : PredShape} (f : ∀{α}, m α → m α)
  [WP m psm] [WP n psn] [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
  [MonadFunctor m n] [MonadFunctor (PredTrans psm) (PredTrans psn)] [WPMonadFunctor m n]
  [ParametricNT m psm f] [MonadMorphism n n (mmap (m:=m) f)]
  : ParametricNT n psn (mmap (m:=m) f) where
  wp_app x x' h := by
    intro Q
    simp only [WPMonadFunctor.monadMap_apply]
    apply WPMonadFunctor.monadMap_mono _ _ _ h
  wp_map_map g x := by apply map_map

instance MonadWithReaderOf.instParametricNTWithReader {m n : Type → Type} (f : ρ → ρ)
  [MonadWithReaderOf ρ m] {psm psn : PredShape} [WP m psm] [WP n psn]
  [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] [MonadFunctor m n] [MonadFunctor (PredTrans psm) (PredTrans psn)] [WPMonadFunctor m n]
  [ParametricNT m psm (MonadWithReaderOf.withReader f)] [MonadMorphism n n (mmap (m:=m) (MonadWithReaderOf.withReader f))]
  : ParametricNT n psn (MonadWithReaderOf.withReader f) where
  wp_app x x' h := by
    intro Q
    simp only [MonadWithReaderOf.withReader, monadMap, WPMonadFunctor.monadMap_apply]
    apply WPMonadFunctor.monadMap_mono _ _ _ h
  wp_map_map g x := by
    simp only [MonadWithReaderOf.withReader, monadMap, ParametricNT.wp_map_map]
    apply (WPMonadFunctor.instParametricNT (MonadWithReaderOf.withReader f)).wp_map_map
-/

lemma ite_app {c:Prop} [Decidable c] (t e : α → β) (a : α) : (if c then t else e) a = if c then t a else e a := by
  split <;> rfl

example :
  wp (m:= ExceptT Nat (StateT Nat (ReaderT Bool Id))) (withTheReader Bool not (do if (← read) then return 0 else return 1)) =
  wp (m:= ExceptT Nat (StateT Nat (ReaderT Bool Id))) (do if (← read) then return 1 else return 0) := by
    ext Q : 2
    simp only [MonadWithReaderOf.withTheReader_apply, MonadWithReaderOf.withReader_apply,
      WP.monadMap_apply, PredTrans.monadMapArg_apply, PredTrans.monadMapExcept_apply,
      WP.popArg_StateT_wp, WP.popExcept_ExceptT_wp, WP.wp1_apply,
      ReaderT.withReader_apply, ReaderT.read_apply, MonadReader.read_apply, WP.bind_apply,
      WP.StateT_run_apply, WP.ExceptT_run_apply, MonadReaderOf.read_apply,
      StateT.monadLift_apply, ReaderT.monadLift_apply, ExceptT.monadLift_apply,
      PredTrans.monadLiftArg_apply, PredTrans.monadLiftExcept_apply,
      MonadMorphism.ite_ite, pure_pure, PredTrans.ite_apply, PredTrans.pure_apply, ite_app]
    simp

end MPL
