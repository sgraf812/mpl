import MPL.WPMonad
import MPL.WPMonadLift

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

-- attribute [simp] LawfulMonadFunctor.monadMap_id LawfulMonadFunctor.monadMap_comp

class WPApp (m : Type → Type) (ps : outParam PredShape) (f : ∀{β}, m β → m β) [WP m ps] where
  F : ∀ {β}, PredTrans ps β → PredTrans ps β
  F_natural (x : m α) (g : α → β) : F (g <$> wp⟦x⟧) = g <$> F (wp⟦x⟧)
  wp_app (x : m α) : wp⟦f x⟧ = F wp⟦x⟧

attribute [simp] WPApp.wp_app WPApp.F_natural WPApp.F

instance StateT.instWPApp [MonadWithReaderOf ρ m] [WP m ps] (f : ∀{β}, m β → m β) [base : WPApp m ps f] : WPApp (StateT σ m) (.arg σ ps) (mmap (m:=m) f) where
  F := mmap (m:=PredTrans ps) base.F
  F_natural x g := by
    calc mmap (m:=PredTrans ps) base.F (g <$> wp⟦x⟧)
      _ = PredTrans.pushArg fun s => base.F ((fun (a, s) => (g a, s)) <$> wp⟦x s⟧) := rfl
      _ = PredTrans.pushArg fun s => (fun (a, s) => (g a, s)) <$> base.F wp⟦x s⟧ := by simp[base.F_natural]
      _ = g <$> PredTrans.pushArg fun s => base.F wp⟦x s⟧ := rfl
  wp_app x := by
    simp[wp, monadMap, MonadFunctor.monadMap, withTheReader, MonadWithReaderOf.withReader, base.wp_app]

instance ReaderT.instWPApp [MonadWithReaderOf ρ m] [WP m ps] (f : ∀{β}, m β → m β) [base : WPApp m ps f] : WPApp (ReaderT σ m) (.arg σ ps) (mmap (m:=m) f) where
  F := mmap (m:=PredTrans ps) base.F
  F_natural x g := by
    calc mmap (m:=PredTrans ps) base.F (g <$> wp⟦x⟧)
      _ = PredTrans.pushArg fun s => base.F ((fun (a, s) => (g a, s)) <$> (·, s) <$> wp⟦x s⟧) := rfl
      _ = PredTrans.pushArg fun s => (fun (a, s) => (g a, s)) <$> base.F ((·, s) <$> wp⟦x s⟧) := by simp[base.F_natural]
      _ = g <$> PredTrans.pushArg fun s => base.F ((·, s) <$> wp⟦x s⟧) := rfl
  wp_app x := by
    simp[wp, monadMap, MonadFunctor.monadMap, withTheReader, MonadWithReaderOf.withReader, base.wp_app, base.F_natural]

theorem thing [WP m ps] (x : ExceptT ε m α) : wp⟦x⟧.popExcept = wp⟦x.run⟧ := by simp[wp, ExceptT.run]
theorem thing2 [WP m ps] (x : StateT σ m α) : wp⟦x⟧.popArg s = wp⟦x.run s⟧ := by simp[wp, StateT.run]

-- the following are just the definitions of wp:
theorem thing3 [WP m ps] (x : ExceptT ε m α) : PredTrans.pushExcept wp⟦x⟧ = wp⟦x⟧ := by simp[wp]
theorem thing4 [WP m ps] (x : StateT σ m α) : PredTrans.pushArg (fun s => wp⟦x s⟧) = wp⟦x⟧ := by simp[wp]

instance ExceptT.instWPApp [MonadWithReaderOf ρ m] [WP m ps] (f : ∀{β}, m β → m β) [base : WPApp m ps f] : WPApp (ExceptT ε m) (.except ε ps) (mmap (m:=m) f) where
  F := mmap (m := PredTrans ps) base.F
  F_natural {α β} x g := by
    calc mmap (m:=PredTrans ps) base.F (g <$> wp⟦x⟧)
      _ = PredTrans.pushExcept (base.F ((g <$> wp⟦x⟧.popExcept) : ExceptT ε (PredTrans ps) β)) := by rfl
      _ = PredTrans.pushExcept (base.F (ExceptT.map g wp⟦x.run⟧)) := by simp[Functor.map, thing]
      _ = PredTrans.pushExcept (base.F (((fun | .ok a => .ok (g a) | .error e => .error e) <$> wp⟦x.run⟧))) := sorry -- incredible how such a simple thing can be so difficult
      _ = PredTrans.pushExcept ((fun | Except.ok a => .ok (g a) | .error e => .error e) <$> base.F wp⟦x.run⟧ : PredTrans ps (Except ε β)) := by simp[base.F_natural]
      _ = g <$> PredTrans.pushExcept (base.F wp⟦x.run⟧) := by
        simp[PredTrans.pushExcept, Functor.map, PredTrans.bind, PredTrans.pure]
        ext Q
        congr
        ext e
        cases e <;> simp
      _ = g <$> PredTrans.pushExcept (base.F wp⟦x⟧.popExcept) := by simp[thing]
  wp_app x := by
    simp[wp, monadMap, MonadFunctor.monadMap, withTheReader, MonadWithReaderOf.withReader, base.wp_app]

instance ReaderT.instWPAppWithReader [WP m ps] (f : ρ → ρ) : WPApp (ReaderT ρ m) (.arg ρ ps) (MonadWithReaderOf.withReader f) where
  F := PredTrans.withReader f
  F_natural x g := rfl
  wp_app x := by simp[wp, MonadWithReaderOf.withReader, PredTrans.withReader]

@[simp]
theorem ReaderT.wp_withReader [Monad m] [WP m psm] [MonadMorphism m (PredTrans psm) wp] :
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

@[simp]
theorem MonadWithReaderOf.wp_withReader2 (x : ReaderT Bool Id Nat) :
  wp (withTheReader Bool f x : ReaderT Bool Id Nat) = pure 0 := by
    simp
    sorry

@[simp]
theorem MonadWithReaderOf.wp_withReader3 (x : StateT Nat (ReaderT Bool Id) Nat) :
  wp (withTheReader Bool f x : StateT Nat (ReaderT Bool Id) Nat) = pure 0 := by
    let inst' := inferInstanceAs (WPApp (StateT Nat (ReaderT Bool Id)) _ (MonadFunctor.monadMap (m:=ReaderT Bool Id) (MonadWithReaderOf.withReader f)))
    simp[inst'.wp_app, WPApp.F]
    simp[WPApp.F]

    sorry

end MPL
