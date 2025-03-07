import MPL.WPMonad
import MPL.WPMonadLift

namespace MPL

@[simp]
theorem ReaderT.wp_withReader [WP m psm] :
  wp (MonadWithReaderOf.withReader f x : ReaderT ρ m α) = PredTrans.withReader f (wp x) := rfl

@[simp]
theorem MonadWithReaderOf.wp_withTheReader [MonadWithReaderOf ρ m] [WP m sh] (f : ρ → ρ) (x : m α) :
  wp (withTheReader ρ f x) = wp (MonadWithReaderOf.withReader f x) := rfl

@[simp]
theorem MonadWithReader.wp_withReader [MonadWithReaderOf ρ m] [WP m sh] (f : ρ → ρ) (x : m α) :
  wp (MonadWithReader.withReader f x) = wp (MonadWithReaderOf.withReader f x) := rfl

@[simp]
theorem MonadWithReaderOf.wp_withReader [MonadWithReaderOf ρ m] [WP m msh] [WP n nsh] [MonadFunctor m n] [MonadFunctor (PredTrans msh) (PredTrans nsh)] (f : ρ → ρ) (x : n α) :
  wp (MonadWithReaderOf.withReader f x) = wp (MonadFunctor.monadMap (m:=m) (MonadWithReaderOf.withReader f) x) := rfl

open MonadFunctor renaming monadMap → mmap

instance ReaderT.instMonadFunctorMorphism [Monad m] [MonadMorphism m _ f] : MonadMorphism (ReaderT ρ m) _ (mmap (m:=m) f) where
  pure_pure := by intro _ _; ext _; simp[MonadFunctor.monadMap, ReaderT.run, pure, ReaderT.pure]
  bind_bind := by intro _ _ _ _; ext _; simp[MonadFunctor.monadMap, ReaderT.run, bind, ReaderT.bind]

instance StateT.instMonadFunctorMorphism [Monad m] [MonadMorphism m _ f] : MonadMorphism (StateT σ m) _ (mmap (m:=m) f) where
  pure_pure := by intro _ _; ext _; simp[MonadFunctor.monadMap, StateT.run, pure, StateT.pure]
  bind_bind := by intro _ _ _ _; ext _; simp[MonadFunctor.monadMap, StateT.run, bind, StateT.bind]

instance ExceptT.instMonadFunctorMorphism [Monad m] [inst : MonadMorphism m _ f] : MonadMorphism (ExceptT ε m) _ (mmap (m:=m) f) where
  pure_pure := by intro _ _; simp[MonadFunctor.monadMap, pure, ExceptT.pure]; erw[inst.pure_pure]; rfl -- URGH: Fix erw
  bind_bind := by intro _ _ _ _; simp[MonadFunctor.monadMap, bind, ExceptT.bind]; erw[inst.bind_bind]; sorry -- URGH: Fix later

instance PredTrans.instMonadFunctorMorphismArg [inst : MonadMorphism (PredTrans ps) (PredTrans ps) f] : MonadMorphism (PredTrans (.arg σ ps)) _ (mmap (m:=PredTrans ps) f) where
  pure_pure := by
    intro α a
    calc mmap (m:=PredTrans ps) f (Pure.pure a)
      _ = pushArg fun s => f (popArg (Pure.pure a) s) := by simp only [MonadFunctor.monadMap]
      _ = pushArg fun s => f (Pure.pure (f:= StateT _ _) a s) := by simp
      _ = pushArg fun s => f (Pure.pure (a, s)) := rfl
      _ = pushArg fun s => Pure.pure (a, s) := by simp
      _ = pushArg (Pure.pure a) := rfl
      _ = Pure.pure a := by simp
  bind_bind := by
    intro α β x k
    calc mmap (m:=PredTrans ps) f (x >>= k)
      _ = pushArg fun s => f (popArg (x >>= k) s) := by simp only [MonadFunctor.monadMap]
      _ = pushArg fun s => f ((popArg x >>= fun a => popArg (k a)) s) := by simp
      _ = pushArg fun s => f (popArg x s >>= fun (a, s) => popArg (k a) s) := by simp[Bind.bind, StateT.bind]
      _ = pushArg fun s => f (popArg x s) >>= fun (a, s) => f (popArg (k a) s) := by simp
      _ = pushArg ((fun s => f (popArg x s)) >>= (fun a s => f (popArg (k a) s))) := by simp+unfoldPartialApp[Bind.bind, StateT.bind]
      _ = pushArg (fun s => f (popArg x s)) >>= fun a => pushArg (fun s => f (popArg (k a) s)) := by simp

instance PredTrans.instMonadFunctorMorphismExcept [inst : MonadMorphism (PredTrans ps) (PredTrans ps) f] : MonadMorphism (PredTrans (.except ε ps)) _ (mmap (m:=PredTrans ps) f) where
  pure_pure := by
    intro α a
    calc mmap (m:=PredTrans ps) f (Pure.pure a)
      _ = pushExcept (f (popExcept (Pure.pure a))) := by simp only [MonadFunctor.monadMap]
      _ = pushExcept (f (Pure.pure (f := ExceptT _ _) a)) := by simp
      _ = pushExcept (f (Pure.pure (.ok a))) := rfl
      _ = pushExcept (Pure.pure (f := PredTrans _) (.ok a)) := by simp
      _ = pushExcept (Pure.pure a) := rfl
      _ = Pure.pure a := by rw[instMonadMorphismPushExcept.pure_pure]
  bind_bind := by
    intro α β x k
    calc mmap (m:=PredTrans ps) f (x >>= k)
      _ = pushExcept (f (popExcept (x >>= k))) := by simp only [MonadFunctor.monadMap]
      _ = pushExcept (f (Bind.bind (m:=ExceptT _ _) (popExcept x) (fun a => popExcept (k a)))) := by simp
      _ = pushExcept (f (popExcept x >>= ExceptT.bindCont fun a => popExcept (k a))) := by simp[Bind.bind, ExceptT.bind, ExceptT.mk]
      _ = pushExcept (Bind.bind (m:=PredTrans _) (f (popExcept x)) fun a => f (ExceptT.bindCont (fun a => popExcept (k a)) a)) := by simp
      _ = pushExcept (Bind.bind (m:=PredTrans _) (f (popExcept x)) fun a => ExceptT.bindCont (fun a => f (popExcept (k a))) a) := by congr; ext x : 1; cases x <;> simp [ExceptT.bindCont]
      _ = pushExcept (Bind.bind (f (popExcept x)) fun a => f (popExcept (k a))) := by simp [Bind.bind, ExceptT.bind, ExceptT.mk]
      _ = Bind.bind (pushExcept (f (popExcept x))) fun a => pushExcept (f (popExcept (k a))) := by rw[instMonadMorphismPushExcept.bind_bind]

class LawfulMonadFunctor (m : semiOutParam (Type → Type)) (n : Type → Type) [Monad n] [MonadFunctor m n] where
  monadMap_id {α} :
    mmap (m:=m) id = (id : n α → n α)
  monadMap_comp {α} (g f : ∀ {β}, m β → m β) :
    mmap (m:=m) (fun a => f (g a)) = fun (x : n α) => mmap (m:=m) f (mmap (m:=m) g x)

/-
theorem LawfulMonadFunctor.monadMap_map {m n : Type → Type} [Monad m] [Monad n] [MonadFunctor m n] [LawfulMonad m] [LawfulMonad n] [LawfulMonadFunctor m n]
    {α β} (f : α → β) (x : m α) :
    MonadFunctor.monadMap (f <$> x) = f <$> (MonadFunctor.monadMap x : n α) := by
    simp[liftM, MonadLift.monadLift, ←bind_pure_comp, monadMap_bind, monadMap_pure]

theorem LawfulMonadFunctor.lift_seq {m n : Type → Type} [Monad m] [Monad n] [MonadLift m n] [LawfulMonad m] [LawfulMonad n] [LawfulMonadFunctor m n]
    {α β} (f : m (α → β)) (x : m α) :
    MonadFunctor.monadMap (f <*> x) = (MonadFunctor.monadMap f : n (α → β)) <*> (MonadFunctor.monadMap x : n α) := by
    simp[liftM, MonadLift.monadLift, ←bind_map, monadMap_bind, lift_map]
-/

instance StateT.instLawfulMonadFunctor [Monad m] [LawfulMonad m] : LawfulMonadFunctor m (StateT σ m) where
  monadMap_id := by intro _; rfl
  monadMap_comp := by intro _; simp only [mmap, implies_true]

instance ReaderT.instLawfulMonadFunctor [Monad m] [LawfulMonad m] : LawfulMonadFunctor m (ReaderT ρ m) where
  monadMap_id := by intro _; rfl
  monadMap_comp := by intro _; simp only [mmap, implies_true]

instance ExceptT.instLawfulMonadFunctor [Monad m] [LawfulMonad m] : LawfulMonadFunctor m (ExceptT ε m) where
  monadMap_id := by intro _; rfl
  monadMap_comp := by intro _; simp only [mmap, implies_true]

instance PredTrans.instLawfulMonadFunctorArg : LawfulMonadFunctor (PredTrans ps) (PredTrans (.arg σ ps)) where
  monadMap_id := by intro _; rfl
  monadMap_comp := by intro _; simp only [mmap, popArg_pushArg, implies_true]

instance PredTrans.instLawfulMonadFunctorDropFail : LawfulMonadFunctor (PredTrans ps) (PredTrans (.except ε ps)) where
  monadMap_id := by intro _; rfl
  monadMap_comp := by intro _; simp only [mmap, popExcept_pushExcept, implies_true]

-- wp is a representation function. We get a Galois Connection
--   α(X) := ⨆{ wp⟦x⟧ | x ∈ X }
--   γ(t) := { x | wp⟦x⟧ ≤ t }
--   α(f)(t) := ⨆{ wp⟦f x⟧ | wp⟦x⟧ ≤ t }
-- wp1⟦f⟧ is exactly α(f).
noncomputable def wp1 {m : Type → Type} {ps : PredShape} [WP m ps] (f : ∀{α}, m α → m α) {α} : PredTrans ps α → PredTrans ps α := fun t =>
  sSup { r | ∃ x, wp⟦x⟧ ≤ t ∧ r = wp⟦f x⟧ }

def wp1.IsGood {m : Type → Type} {ps : PredShape} [WP m ps] (f : ∀{α}, m α → m α) : Prop :=
  ∀ {α} (x x' : m α), wp⟦x⟧ ≤ wp⟦x'⟧ → wp⟦f x⟧ ≤ wp⟦f x'⟧

class WPApp (m : Type → Type) (ps : outParam PredShape) [WP m ps] (f : ∀{α}, m α → m α) where
  wp_app : ∀ {α} (x x' : m α), wp⟦x⟧ ≤ wp⟦x'⟧ → wp⟦f x⟧ ≤ wp⟦f x'⟧

instance ReaderT.instWPAppWithReader {m : Type → Type} {ps : PredShape} [WP m ps] (f : ρ → ρ) : WPApp (ReaderT ρ m) (.arg ρ ps) (MonadWithReaderOf.withReader f) where
  wp_app x x' h := by simp; apply PredTrans.withReader_mono f _ _ h

instance ReaderT.instWPApp [MonadWithReaderOf ρ m] [WP m ps] (f : ∀{β}, m β → m β) [base : WPApp m ps f] : WPApp (ReaderT ρ m) (.arg ρ ps) (mmap (m:=m) f) where
  wp_app x x' h := by
    intro Q r
    apply base.wp_app
    intro Q
    apply h (fun a _ => Q.1 a, Q.2)

instance StateT.instWPApp [MonadWithReaderOf ρ m] [WP m ps] (f : ∀{β}, m β → m β) [base : WPApp m ps f] : WPApp (StateT σ m) (.arg σ ps) (mmap (m:=m) f) where
  wp_app x x' h := by
    intro Q s
    apply base.wp_app
    intro Q
    apply h (fun a s => Q.1 (a, s), Q.2)

@[simp]
lemma except_eta {r : Sort u} (Q : Except ε α → r) : (fun | Except.ok a => Q (Except.ok a) | Except.error e => Q (Except.error e)) = Q := by
  ext x; cases x <;> rfl

instance ExceptT.instWPApp [MonadWithReaderOf ρ m] [WP m ps] (f : ∀{β}, m β → m β) [base : WPApp m ps f] : WPApp (ExceptT ε m) (.except ε ps) (mmap (m:=m) f) where
  wp_app {α} x x' h := by
    intro Q
    apply base.wp_app
    intro Q
    replace h := h (fun a => Q.1 (.ok a), fun e => Q.1 (.error e), Q.2)
    simp[wp, PredTrans.pushExcept] at h
    have heta : Q = (fun x => match x with | Except.ok a => Q.1 (Except.ok a) | Except.error e => Q.1 (Except.error e), Q.2) := by
      (ext x; cases x) <;> rfl
    apply le_trans _ (le_trans h _)
    · conv => lhs; rw [heta]
      sorry -- apply le_rfl -- Sigh. need to prove that LE (PreCond (.except ε ps)) = LE (PreCond ps)
    · conv => rhs; rw [heta]
      sorry -- apply le_rfl -- Sigh. need to prove that LE (PreCond (.except ε ps)) = LE (PreCond ps)

@[simp]
theorem wp1_apply {m : Type → Type} {ps : PredShape} [WP m ps] (f : ∀{α}, m α → m α) [WPApp m ps f] (x : m α) :
  wp1 (m:=m) f wp⟦x⟧ = wp⟦f x⟧ := by
    apply le_antisymm
    · apply sSup_le
      intro r ⟨x, hwpx, hwr⟩
      subst hwr
      apply WPApp.wp_app
      trivial
    · apply le_sSup
      use x, le_rfl

theorem ReaderT.wp_withReader2 [WP m psm] (f : ρ → ρ) {α} :
  wp1 (α:=α) (m := ReaderT ρ m) (MonadWithReaderOf.withReader f) ≤ PredTrans.withReader f := by
    intro t
    apply sSup_le
    intro r ⟨x, hwpx, hwr⟩
    subst hwr
    simp only [wp_withReader]
    apply PredTrans.withReader_mono
    trivial

example [WP m psm] (f : ρ → ρ) {α} :
  wp1 (α:=α) (m := ReaderT ρ m) (MonadWithReaderOf.withReader f) ≥ PredTrans.withReader f := by
    intro t
    match Classical.exists_or_forall_not (fun (x : ReaderT ρ m α) => wp⟦x⟧ ≤ t) with
    | .inl ⟨x, h⟩ => apply le_sSup; use x, h; sorry -- close enough?! but not really
    | .inr h => sorry -- no chance. The RHS is ⊥, but cannot show that t is bottom from h. Or can we?

class WPMonadFunctor (m : Type → Type) (n : Type → Type) [WP m psm] [WP n psn] [MonadFunctor m n] [MonadFunctor (PredTrans psm) (PredTrans psn)] where
  wp_monadFunctor (f : ∀{β}, m β → m β) [WPApp m psm f] {α} (x : n α) :
    wp⟦mmap (m:=m) f x⟧ = mmap (m:=PredTrans psm) (wp1 (m:=m) f) wp⟦x⟧
export WPMonadFunctor (wp_monadFunctor)
attribute [simp] WPMonadFunctor.wp_monadFunctor

instance StateT.instWPMonadFunctor [WP m ps] : WPMonadFunctor m (StateT σ m)  where
  wp_monadFunctor f x := by
    simp only [wp, MonadFunctor.monadMap, PredTrans.popArg_pushArg, wp1_apply, implies_true]

instance ReaderT.instWPMonadFunctor [WP m ps] : WPMonadFunctor m (StateT σ m)  where
  wp_monadFunctor f x := by
    simp only [wp, MonadFunctor.monadMap, PredTrans.popArg_pushArg, wp1_apply, implies_true]

instance ExceptT.instWPMonadFunctor [WP m ps] : WPMonadFunctor m (ExceptT ε m)  where
  wp_monadFunctor f x := by
    simp only [wp, MonadFunctor.monadMap, PredTrans.popExcept_pushExcept, wp1_apply, implies_true]

@[simp]
theorem MonadWithReaderOf.wp_withReader2 (x : ReaderT Bool Id Nat) :
  wp (withTheReader Bool f x : ReaderT Bool Id Nat) = pure 0 := by
    simp
    sorry

/-
theorem wp1.pure_pure {m : Type → Type} {ps : PredShape} [WP m ps] [Monad m] [MonadMorphism m _ wp] (f : ∀ {α}, m α → m α) [WPApp m ps f] [MonadMorphism m _ f] (a : α) :
  wp1 (m:=m) f (pure a) = pure a := by
    apply le_antisymm
    · apply sSup_le
      intro r ⟨x, hwpx, hwr⟩
      subst hwr
      replace hwpx : wp⟦x⟧ ≤ wp⟦pure (f:=m) a⟧ := by simp[hwpx]
      apply le_trans (WPApp.wp_app _ _ hwpx)
      simp
    · apply le_sSup
      use pure a
      simp

theorem wp1.bind_bind {m : Type → Type} {ps : PredShape} [WP m ps] [Monad m] [MonadMorphism m _ wp] (f : ∀ {α}, m α → m α) [WPApp m ps f] [MonadMorphism m _ f] (t : PredTrans ps α) (k : α → PredTrans ps β) :
  wp1 (m:=m) f (do let a ← x; k a) = (do let a ← wp1 (m:=m) f t; wp1 (m:=m) f (k a)) := by
    apply le_antisymm
    · apply sSup_le
      intro r ⟨x, hwpx, hwr⟩
      subst hwr
      sorry
      -- replace hwpx : wp⟦x⟧ ≤ wp⟦do let a ← t; k a⟧ := by simp[hwpx]
      -- apply le_trans (WPApp.wp_app _ _ hwpx)
      -- simp
    · apply le_sSup
      use (do let a ← t; k a)
      simp
-/

attribute [simp] PredTrans.instMonadFunctorArg
attribute [simp] PredTrans.instMonadFunctorExcept

@[simp]
lemma ite_app {c:Prop} [Decidable c] (t e : α → β) (a : α) : (if c then t else e) a = if c then t a else e a := by
  split <;> rfl

example :
  wp (m:= StateT Nat (ReaderT Bool Id)) (withTheReader Bool not (do if (← read) then return 0 else return 1)) =
  wp (m:= StateT Nat (ReaderT Bool Id)) (do if (← read) then return 1 else return 0) := by
    ext Q : 2
    simp only [MonadWithReaderOf.wp_withTheReader, MonadWithReaderOf.wp_withReader, wp_monadFunctor, PredTrans.instMonadFunctorArg, WP.popArg_wp, wp1_apply]
    simp

class WPDefinable {ps : PredShape} (t : PredTrans ps α) {m : Type → Type} [WP m ps] (x : outParam (m α)) where
  wp_definable : t = wp (m:=m) x

instance (x : m α) [WP m ps] : WPDefinable wp⟦x⟧ x where
  wp_definable := rfl

instance (c : Prop) [Decidable c] (x₁ x₂ : m α) (t₁ t₂ : PredTrans ps α) [WP m ps] [WPDefinable t₁ x₁] [WPDefinable t₂ x₂] : WPDefinable (if c then t₁ else t₂) (if c then x₁ else x₂) where
  wp_definable := by split <;> exact WPDefinable.wp_definable

instance (a : α) [WP m ps] [Monad m] [MonadMorphism m _ wp] : WPDefinable (m:=m) (pure a) (pure a) where
  wp_definable := (pure_pure a).symm

instance (x : m α) (t : PredTrans ps α) (f : α → β) [WP m ps] [Monad m] [LawfulMonad m] [MonadMorphism m _ wp] [base : WPDefinable t x] : WPDefinable (f <$> t) (f <$> x) where
  wp_definable := by simp[base.wp_definable]

instance (x : m α) (t : PredTrans ps α) (f : α → PredTrans ps β) (g : α → m β) [WP m ps] [Monad m] [LawfulMonad m] [MonadMorphism m _ wp] [base₁ : WPDefinable t x] [base₂ : ∀ a, WPDefinable (f a) (g a)] : WPDefinable (t >>= f) (x >>= g) where
  wp_definable := by simp[base₁.wp_definable]; congr; ext a : 1; exact (base₂ a).wp_definable

instance (x : StateT σ m α) (t : PredTrans (.arg σ ps) α) [WP m ps] [Monad m] [LawfulMonad m] [MonadMorphism m _ wp] [base : WPDefinable t x] : WPDefinable (t.popArg s) (x.run s) where
  wp_definable := by simp[base.wp_definable]

instance (x : StateT σ m α) (t : StateT σ (PredTrans ps) α) [WP m ps] [Monad m] [LawfulMonad m] [MonadMorphism m _ wp] [base : WPDefinable (PredTrans.pushArg t) x] : WPDefinable (t s) (x.run s) where
  wp_definable := by
    ext Q
    exact congrArg (fun t => t.apply (fun a s => Q.1 (a, s), Q.2) s) base.wp_definable;

instance (x : m α) (t : PredTrans psm α) [WP m psm] [WP n psn] [MonadLift m n] [MonadLift (PredTrans psm) (PredTrans psn)] [base : WPDefinable t x] [WPMonadLift m n psm psn] : WPDefinable (m:=n) (MonadLift.monadLift (m:=PredTrans psm) t) (MonadLift.monadLift (m:=m) x) where
  wp_definable := by simp[base.wp_definable]

instance [WP m ps] [Monad m] [MonadMorphism m _ wp] : WPDefinable (m := StateT σ m) PredTrans.get MonadStateOf.get where
  wp_definable := by simp

instance (s : σ) [WP m ps] [Monad m] [MonadMorphism m _ wp] : WPDefinable (m := StateT σ m) (PredTrans.set s) (MonadState.set s) where
  wp_definable := by simp

instance (f : σ → α × σ) [WP m ps] [Monad m] [MonadMorphism m _ wp] : WPDefinable (m := StateT σ m) (PredTrans.modifyGet f) (MonadState.modifyGet f) where
  wp_definable := by simp

instance [WP m ps] [Monad m] [MonadMorphism m _ wp] : WPDefinable (m := ReaderT ρ m) PredTrans.get MonadReaderOf.read where
  wp_definable := by simp

@[simp 1000000000000000000]
theorem wp1_apply2 {m : Type → Type} {ps : PredShape} [WP m ps] (f : ∀{α}, m α → m α) [WPApp m ps f] (t : PredTrans ps α) (x : m α) [inst : WPDefinable t x] :
  wp1 (m:=m) f t = wp⟦f x⟧ := by
    apply le_antisymm
    · apply sSup_le
      intro r ⟨x, hwpx, hwr⟩
      have := inst.wp_definable
      subst hwr this
      apply WPApp.wp_app
      trivial
    · apply le_sSup
      use x, le_of_eq inst.wp_definable.symm

/-
set_option diagnostics true in
set_option trace.Meta.synthInstance true in
set_option synthInstance.maxSize 1000 in
set_option maxHeartbeats 1000000000000000000 in
#synth ∀ s, @WPDefinable (Prod Nat Nat) (PredShape.arg Bool PredShape.pure)
    (@bind (StateT Nat (PredTrans (PredShape.arg Bool PredShape.pure)))
      (@Monad.toBind (StateT Nat (PredTrans (PredShape.arg Bool PredShape.pure)))
        (@StateT.instMonad Nat (PredTrans (PredShape.arg Bool PredShape.pure))
          (@instMonadPredTrans (PredShape.arg Bool PredShape.pure))))
      Bool Nat
      (@PredTrans.popArg Nat (PredShape.arg Bool PredShape.pure) Bool
        (@MonadLift.monadLift (PredTrans (PredShape.arg Bool PredShape.pure))
          (PredTrans (PredShape.arg Nat (PredShape.arg Bool PredShape.pure)))
          (@PredTrans.instMonadLiftArg (PredShape.arg Bool PredShape.pure) Nat) Bool
          (@PredTrans.get PredShape.pure Bool)))
      (fun a =>
        @ite (StateT Nat (PredTrans (PredShape.arg Bool PredShape.pure)) Nat) (@Eq Bool a true)
          (instDecidableEqBool a true)
          (@pure (StateT Nat (PredTrans (PredShape.arg Bool PredShape.pure)))
            (@Applicative.toPure (StateT Nat (PredTrans (PredShape.arg Bool PredShape.pure)))
              (@Monad.toApplicative (StateT Nat (PredTrans (PredShape.arg Bool PredShape.pure)))
                (@StateT.instMonad Nat (PredTrans (PredShape.arg Bool PredShape.pure))
                  (@instMonadPredTrans (PredShape.arg Bool PredShape.pure)))))
            Nat (@OfNat.ofNat Nat 0 (instOfNatNat 0)))
          (@pure (StateT Nat (PredTrans (PredShape.arg Bool PredShape.pure)))
            (@Applicative.toPure (StateT Nat (PredTrans (PredShape.arg Bool PredShape.pure)))
              (@Monad.toApplicative (StateT Nat (PredTrans (PredShape.arg Bool PredShape.pure)))
                (@StateT.instMonad Nat (PredTrans (PredShape.arg Bool PredShape.pure))
                  (@instMonadPredTrans (PredShape.arg Bool PredShape.pure)))))
            Nat (@OfNat.ofNat Nat 1 (instOfNatNat 1))))
      s)
    (ReaderT Bool Id) (@Reader.instWP Bool) _
example :
  wp (m:= StateT Nat (ReaderT Bool Id)) (withTheReader Bool not (do if (← read) then return 0 else return 1)) =
  wp (m:= StateT Nat (ReaderT Bool Id)) (do if (← read) then return 1 else return 0) := by
    ext Q : 2
    simp
    set_option trace.Meta.synthInstance true in
    set_option trace.Meta.synthInstance.tryResolve true in
    set_option pp.explicit true in
    conv in wp1 _ _ => rw[wp1_apply2]
    simp only [MonadWithReaderOf.wp_withTheReader, MonadWithReaderOf.wp_withReader, wp_monadFunctor,
      PredTrans.instMonadFunctorArg, bind_bind, MonadReader.wp_read, MonadReaderOf.wp_read,
      ReaderT.wp_read, MonadMorphism.ite_ite, pure_pure, PredTrans.pushArg_apply,
      PredTrans.bind_apply, PredTrans.ite_apply, PredTrans.pure_apply, PredTrans.monadLiftArg_apply,
      ite_app, PredTrans.get_apply]
    simp only [MonadWithReaderOf.wp_withTheReader, MonadWithReaderOf.wp_withReader, wp_monadFunctor,
      PredTrans.instMonadFunctorArg, bind_bind, MonadReader.wp_read, MonadReaderOf.wp_read,
      ReaderT.wp_read, MonadMorphism.ite_ite, pure_pure, PredTrans.pushArg_apply,
      PredTrans.bind_apply, PredTrans.ite_apply, PredTrans.pure_apply, PredTrans.monadLiftArg_apply,
      ite_app, wp1_apply2]
    simp only [MonadWithReaderOf.wp_withTheReader, MonadWithReaderOf.wp_withReader, wp_monadFunctor, PredTrans.instMonadFunctorArg]
    simp only [wp1_apply2]
    simp only [MonadWithReaderOf.wp_withTheReader, MonadWithReaderOf.wp_withReader, wp_monadFunctor, PredTrans.instMonadFunctorArg, WP.popArg_wp, wp1_apply]
    simp
-/

end MPL
