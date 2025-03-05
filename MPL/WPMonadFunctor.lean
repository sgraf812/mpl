import MPL.WPMonad

namespace MPL

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

attribute [simp] LawfulMonadFunctor.monadMap_id LawfulMonadFunctor.monadMap_comp

example : ∀ (m : Type → Type) (f : ∀{β}, m β → m β) (f' : ∀{β}, PredTrans ps β → PredTrans ps β) (x : m α) [WP m ps],
  wp⟦f x⟧ = f' wp⟦x⟧ := sorry

noncomputable def blah {m : Type → Type} [WP m ps] (f : ∀{β}, m β → m β) : ∀{β}, PredTrans ps β → PredTrans ps β := fun t =>
  sInf { t' | ∃ x, t ≤ wp⟦x⟧ ∧ t' = wp⟦f x⟧  }

theorem blah_spec {m : Type → Type} [WP m ps] (f : ∀{β}, m β → m β) (x : m α) : blah (m:=m) f wp⟦x⟧ = wp⟦f x⟧ := by
  simp[blah]
  apply le_antisymm
  · apply sInf_le
    use x
  · apply le_sInf
    intro t' ⟨x', ⟨hx, ht⟩⟩
    subst ht

class WPMonadFunctor (m : semiOutParam (Type → Type)) (n : Type → Type) (psm : outParam PredShape) (psn : outParam PredShape)
  [WP m psm] [WP n psn] [MonadFunctor m n] [MonadFunctor (PredTrans psm) (PredTrans psn)] where
  wp_monadFunctor {x : n α} :
    wp (MonadFunctor.monadMap f x : n α) = MonadFunctor.monadMap (wp1 f) (wp x)

export WPMonadLift (wp_monadLift)
attribute [simp] wp_monadLift

@[simp]
theorem ReaderT.wp_withReader [Monad m] [WP m psm] [MonadMorphism m (PredTrans psm) wp] :
  wp (MonadWithReaderOf.withReader f x : ReaderT ρ m α) = PredTrans.withReader f (wp x) := rfl

@[simp]
theorem MonadWithReaderOf.wp_withTheReader [MonadWithReaderOf ρ m] [WP m sh] :
  wp (withTheReader ρ f x : m ρ) = wp (MonadWithReaderOf.withReader f x : m ρ) := rfl

@[simp]
theorem MonadWithReader.wp_withReader [MonadWithReaderOf ρ m] [WP m sh] :
  wp (MonadWithReader.withReader f x : m ρ) = wp (MonadWithReaderOf.withReader f x : m ρ) := rfl

@[simp]
theorem MonadWithReaderOf.wp_withReader [MonadWithReaderOf ρ m] [WP m msh] [WP n nsh] [MonadFunctor m n] [MonadFunctor (PredTrans msh) (PredTrans nsh)] :
  wp (withTheReader ρ f x : n ρ) = monadMap (m:= PredTrans msh) _ (wp x) := by
    simp[withReader, withTheReader, MonadWithReaderOf.withReader]
-- wp : ∀ ρ, n ρ → PredTrans nsh ρ
-- wp : ∀ ρ, n ρ → PredTrans nsh ρ

@[simp]
theorem MonadWithReaderOf.wp_withReader2 (x : StateT Nat (ReaderT Bool Id) α) :
  wp (withTheReader Bool f x : StateT Nat (ReaderT Bool Id) α) = monadMap (PredTrans.withReader f) (wp x) := by
    simp[withReader, withTheReader, MonadWithReaderOf.withReader]
    simp[monadMap]

end MPL
