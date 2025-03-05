namespace MPL

class MonadMorphism (m : Type → Type) (n : Type → Type) [Monad m] [Monad n] (morph : ∀ {α}, m α → n α) where
  pure_pure : ∀ {α} (a : α), morph (pure a) = pure a
  bind_bind : ∀ {α β} (x : m α) (f : α → m β), morph (do let a ← x; f a) = do let a ← morph x; morph (f a)

attribute [simp] MonadMorphism.pure_pure MonadMorphism.bind_bind

@[simp]
theorem MonadMorphism.map_map [Monad m] [Monad n] [MonadMorphism m n morph] [LawfulMonad m] [LawfulMonad n] (f : α → β) (x : m α) :
  morph (f <$> x) = f <$> morph x := by
    simp [← bind_pure_comp, bind_bind, pure_pure]

@[simp]
theorem MonadMorphism.seq_seq [Monad m] [Monad n] [MonadMorphism m n morph] [LawfulMonad m] [LawfulMonad n] (f : m (α → β)) (x : m α) :
  morph (f <*> x) = morph f <*> morph x := by
    simp [← bind_map, bind_bind, map_map]

@[simp]
theorem MonadMorphism.dite_dite {c : Prop} [Decidable c] {t : c → m α} {e : ¬c → m α} [Monad m] [Monad n] [MonadMorphism m n morph] :
  morph (dite c t e) = if h : c then morph (t h) else morph (e h) := by
    split <;> simp

@[simp]
theorem MonadMorphism.ite_ite {c : Prop} [Decidable c] {t : m α} {e : m α} [Monad m] [Monad n] [MonadMorphism m n morph] :
  morph (ite c t e) = if c then morph t else morph e := by
  split <;> simp

export MonadMorphism (pure_pure bind_bind map_map seq_seq)

end MPL
