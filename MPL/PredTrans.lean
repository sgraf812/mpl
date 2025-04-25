/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
import MPL.MonadMorphism
import MPL.PostCond

/-!
# Predicate transformers for arbitrary postcondition shapes

This module defines the type `PredTrans ps` of *predicate transformers* for a given `ps :
PostShape`.
`PredTrans` forms the semantic domain of the weakest precondition interpretation
`WP` in which we interpret monadic programs.

A predicate transformer `x : PredTrans ps α` is a function that takes a postcondition
`Q : PostCond α ps` and returns a precondition `x.apply Q : PreCond ps`, with the additional
monotonicity property that the precondition is stronger the stronger the postcondition is:
`Q₁ ⊢ₚ Q₂ → x.apply Q₁ ⊢ₛ x.apply Q₂`.

Since `PredTrans` itself forms a monad, we can interpret monadic programs by writing
a monad morphism into `PredTrans`; this is exactly what `WP` encodes.
This module defines interpretations of common monadic operations, such as `get`, `throw`,
`liftM`, etc.
-/

namespace MPL

/-- The stronger the postcondition, the stronger the transformed precondition. -/
def PredTrans.Mono {ps : PostShape} {α : Type} (x : PostCond α ps → PreCond ps) : Prop :=
  ∀ Q₁ Q₂, (Q₁ ⊢ₚ Q₂) → (x Q₁) ⊢ₛ (x Q₂)

/--
  The type of predicate transformers for a given `ps : PostShape` and return type `α : Type`.
  A predicate transformer `x : PredTrans ps α` is a function that takes a postcondition
  `Q : PostCond α ps` and returns a precondition `x.apply Q : PreCond ps`, with the additional
  monotonicity property that the precondition is stronger the stronger the postcondition is:
  `Q₁ ⊢ₚ Q₂ → x.apply Q₁ ⊢ₛ x.apply Q₂`.
 -/
@[ext]
structure PredTrans (ps : PostShape) (α : Type) : Type where
  apply : PostCond α ps → PreCond ps
  mono : PredTrans.Mono apply

def PredTrans.const {ps : PostShape} {α : Type} (p : PreCond ps) : PredTrans ps α :=
  ⟨fun _ => p, fun _ _ _ => SPred.entails.refl _⟩

/--
  Given a fixed postcondition, the *stronger* predicate transformer will yield a
  *weaker* precondition.
-/
def PredTrans.le {ps : PostShape} {α : Type} (x y : PredTrans ps α) : Prop :=
  ∀ Q, y.apply Q ⊢ₛ x.apply Q -- the weaker the precondition, the smaller the PredTrans
instance : LE (PredTrans ps α) := ⟨PredTrans.le⟩

def PredTrans.pure {ps : PostShape} {α : Type} (a : α) : PredTrans ps α :=
  { apply := fun Q => Q.1 a, mono := by intro _ _ h; apply h.1 }

def PredTrans.bind {ps : PostShape} {α β : Type} (x : PredTrans ps α) (f : α → PredTrans ps β) : PredTrans ps β :=
  { apply := fun Q => x.apply (fun a => (f a).apply Q, Q.2), mono := by
      intro Q₁ Q₂ h
      rw [apply]
      apply x.mono
      refine ⟨?_, h.2⟩
      intro a
      apply (f a).mono
      exact h }

instance : Monad (PredTrans ps) where
  pure := PredTrans.pure
  bind := PredTrans.bind

@[simp]
theorem PredTrans.pure_apply {ps : PostShape} {α : Type} (a : α) (Q : PostCond α ps) :
  (Pure.pure a : PredTrans ps α).apply Q = Q.1 a := by rfl

@[simp]
theorem PredTrans.map_apply {ps : PostShape} {α β : Type} (f : α → β) (x : PredTrans ps α) (Q : PostCond β ps) :
  (f <$> x).apply Q = x.apply (fun a => Q.1 (f a), Q.2) := by rfl

@[simp]
theorem PredTrans.bind_apply {ps : PostShape} {α β : Type} (x : PredTrans ps α) (f : α → PredTrans ps β) (Q : PostCond β ps) :
  (x >>= f).apply Q = x.apply (fun a => (f a).apply Q, Q.2) := by rfl

@[simp]
theorem PredTrans.seq_apply {ps : PostShape} {α β : Type} (f : PredTrans ps (α → β)) (x : PredTrans ps α) (Q : PostCond β ps) :
  (f <*> x).apply Q = f.apply (fun g => x.apply (fun a => Q.1 (g a), Q.2), Q.2) := by rfl

theorem PredTrans.bind_mono {ps : PostShape} {α β : Type} {x y : PredTrans ps α} {f : α → PredTrans ps β}
  (h : x ≤ y) : x >>= f ≤ y >>= f := by intro Q; exact (h (_, Q.2))

instance PredTrans.instLawfulMonad : LawfulMonad (PredTrans ps) :=
  LawfulMonad.mk' (PredTrans ps)
    (id_map := by simp +unfoldPartialApp [Functor.map, Bind.bind, PredTrans.bind, Pure.pure, PredTrans.pure])
    (pure_bind := by simp +unfoldPartialApp [Bind.bind, PredTrans.bind, Pure.pure, PredTrans.pure])
    (bind_assoc := by simp +unfoldPartialApp [Bind.bind, PredTrans.bind])

def PredTrans.get {ps : PostShape} {σ : Type} : PredTrans (.arg σ ps) σ :=
  { apply := fun Q s => Q.1 s s, mono := by
      intro Q₁ Q₂ h
      simp only [apply]
      intro s
      exact h.1 s s }

def PredTrans.set {ps : PostShape} {σ : Type} (s : σ) : PredTrans (.arg σ ps) PUnit :=
  { apply := fun Q _ => Q.1 ⟨⟩ s, mono := by
      intro Q₁ Q₂ h
      simp only [apply]
      intro _
      exact h.1 ⟨⟩ s }

def PredTrans.throw {ps : PostShape} {ε : Type} (e : ε) : PredTrans (.except ε ps) α :=
  { apply := fun Q => Q.2.1 e, mono := by
      intro Q₁ Q₂ h
      simp only [apply]
      exact h.2.1 e }

def PredTrans.tryCatch {ps : PostShape} {ε : Type} (x : PredTrans (.except ε ps) α) (handle : ε → PredTrans (.except ε ps) α) : PredTrans (.except ε ps) α :=
  { apply := fun Q => x.apply (Q.1, fun e => (handle e).apply Q, Q.2.2), mono := by
      intro Q₁ Q₂ h
      apply x.mono
      refine ⟨h.1, ?_, h.2.2⟩
      intro e
      apply (handle e).mono _ _ h }

@[simp]
def PredTrans.modify {ps : PostShape} {σ : Type} (f : σ → σ) : PredTrans (.arg σ ps) PUnit := do
  let s ← PredTrans.get
  PredTrans.set (f s)

-- The interpretation of `StateT σ (PredTrans ps) α` into `PredTrans (.arg σ ps) α`.
-- Think: modifyGetM
def PredTrans.pushArg {ps : PostShape} {σ : Type} {α : Type} (x : StateT σ (PredTrans ps) α) : PredTrans (.arg σ ps) α :=
  { apply := fun Q s => (x s).apply (fun (a, s) => Q.1 a s, Q.2), mono := by
      intro Q₁ Q₂ h
      simp only [apply]
      intro s
      apply (x s).mono
      exact ⟨fun p => h.1 p.1 p.2, h.2⟩ }

def PredTrans.popArg {ps : PostShape} {α} (x : PredTrans (.arg σ ps) α) : StateT σ (PredTrans ps) α := fun s =>
  { apply Q := x.apply (fun r s' => Q.1 (r, s'), Q.2) s,
    mono := by
      intro Q₁ Q₂ h
      apply x.mono
      refine ⟨?_, h.2⟩
      intro r s'
      apply h.1 }

-- The interpretation of `ExceptT ε (PredTrans ps) α` into `PredTrans (.except ε ps) α`
def PredTrans.pushExcept {ps : PostShape} {α ε} (x : ExceptT ε (PredTrans ps) α) : PredTrans (.except ε ps) α :=
  { apply Q := x.apply (fun | .ok a => Q.1 a | .error e => Q.2.1 e, Q.2.2),
    mono := by
      intro Q₁ Q₂ h
      apply x.mono
      simp
      exact ⟨fun | .ok a => h.1 a | .error e => h.2.1 e, h.2.2⟩ }

def PredTrans.popExcept {ps : PostShape} {α} (x : PredTrans (.except ε ps) α) : ExceptT ε (PredTrans ps) α :=
  { apply Q := x.apply (fun a => Q.1 (.ok a), fun e => Q.1 (.error e), Q.2),
    mono := by
      intro Q₁ Q₂ h
      apply x.mono
      exact ⟨fun a => h.1 (.ok a), fun e => h.1 (.error e), h.2⟩ }

def PredTrans.modifyGet {ps : PostShape} {σ : Type} {α : Type} (f : σ → α × σ) : PredTrans (.arg σ ps) α :=
  pushArg (fun a => pure (f a))

@[simp]
theorem PredTrans.modifyGet_pure {ps : PostShape} {σ : Type} {α : Type} (a : α) :
  PredTrans.modifyGet (ps:=ps) (σ:=σ) (fun s => (a, s)) = Pure.pure a := rfl

def PredTrans.withReader {ps : PostShape} {σ : Type} (f : σ → σ) (x : PredTrans (.arg σ ps) α) : PredTrans (.arg σ ps) α :=
  PredTrans.pushArg fun r => do let (a, _) ← PredTrans.popArg x (f r); Pure.pure (a, r)

theorem PredTrans.withReader_mono {ps : PostShape} {σ : Type} (f : σ → σ) (x x' : PredTrans (.arg σ ps) α) :
  x ≤ x' → withReader f x ≤ withReader f x' := by intro h Q r; apply h

instance PredTrans.instMonadLiftArg : MonadLift (PredTrans m) (PredTrans (.arg σ m)) where
  monadLift x := PredTrans.pushArg (StateT.lift x)

instance PredTrans.instMonadLiftExcept : MonadLift (PredTrans m) (PredTrans (.except ε m)) where
  monadLift x := PredTrans.pushExcept (ExceptT.lift x)

instance PredTrans.instMonadFunctorArg : MonadFunctor (PredTrans m) (PredTrans (.arg σ m)) where
  monadMap f x := PredTrans.pushArg (fun s => f (PredTrans.popArg x s))

instance PredTrans.instMonadFunctorExcept : MonadFunctor (PredTrans m) (PredTrans (.except ε m)) where
  monadMap f x := PredTrans.pushExcept (f x.popExcept)

@[simp]
def PredTrans.get_apply {ps} {σ : Type} {Q : PostCond σ (.arg σ ps)} :
  PredTrans.get.apply Q = fun s => Q.1 s s := rfl

@[simp]
def PredTrans.set_apply {ps} {σ : Type} {Q : PostCond PUnit (.arg σ ps)} (s : σ) :
  (PredTrans.set s).apply Q = fun _ => Q.1 ⟨⟩ s := rfl

@[simp]
def PredTrans.modifyGet_apply {ps} {α : Type} {σ : Type} {Q : PostCond α (.arg σ ps)} (f : σ → α × σ) :
  (PredTrans.modifyGet f).apply Q = fun s => let ⟨a, s⟩ := f s; Q.1 a s := rfl

@[simp]
def PredTrans.pushArg_apply {ps} {α : Type} {σ : Type} {Q : PostCond α (.arg σ ps)} (f : σ → PredTrans ps (α × σ)) :
  (PredTrans.pushArg f).apply Q = fun s => (f s).apply (fun ⟨a, s⟩ => Q.1 a s, Q.2) := rfl

@[simp]
def PredTrans.throw_apply {ps} {α ε : Type} {Q : PostCond α (.except ε ps)} (e : ε) :
  (PredTrans.throw e).apply Q = Q.2.1 e := rfl

@[simp]
def PredTrans.pushExcept_apply {ps} {α ε} {Q : PostCond α (.except ε ps)} (x : PredTrans ps (Except ε α)) :
  (PredTrans.pushExcept x).apply Q = x.apply (fun | .ok a => Q.1 a | .error e => Q.2.1 e, Q.2.2) := rfl

@[simp]
def PredTrans.dite_apply {ps} {Q : PostCond α ps} (c : Prop) [Decidable c] (t : c → PredTrans ps α) (e : ¬ c → PredTrans ps α) :
  (if h : c then t h else e h).apply Q = if h : c then (t h).apply Q else (e h).apply Q := by split <;> rfl

@[simp]
def PredTrans.ite_apply {ps} {Q : PostCond α ps} (c : Prop) [Decidable c] (t : PredTrans ps α) (e : PredTrans ps α) :
  (if c then t else e).apply Q = if c then t.apply Q else e.apply Q := by split <;> rfl

@[simp]
def PredTrans.monadLiftArg_apply {ps} {Q : PostCond α (.arg σ ps)} (t : PredTrans ps α) :
  (MonadLift.monadLift t : PredTrans (.arg σ ps) α).apply Q = fun s => t.apply (fun a => Q.1 a s, Q.2) := rfl

@[simp]
def PredTrans.monadLiftExcept_apply {ps} {Q : PostCond α (.except ε ps)} (t : PredTrans ps α) :
  (MonadLift.monadLift t : PredTrans (.except ε ps) α).apply Q = t.apply (fun a => Q.1 a, Q.2.2) := rfl

@[simp]
def PredTrans.monadMapArg_apply {ps} {Q : PostCond α (.arg σ ps)} (f : ∀{β}, PredTrans ps β → PredTrans ps β) (t : PredTrans (.arg σ ps) α) :
  (MonadFunctor.monadMap (m:=PredTrans ps) f t).apply Q = fun s => (f (t.popArg s)).apply (fun (a, s) => Q.1 a s, Q.2) := rfl

@[simp]
def PredTrans.monadMapExcept_apply {ps} {Q : PostCond α (.except ε ps)} (f : ∀{β}, PredTrans ps β → PredTrans ps β) (t : PredTrans (.except ε ps) α) :
  (MonadFunctor.monadMap (m:=PredTrans ps) f t).apply Q = (f t.popExcept).apply (fun | .ok a => Q.1 a | .error e => Q.2.1 e, Q.2.2) := rfl

@[simp]
def PredTrans.popArg_apply {ps} {Q : PostCond (α × σ) ps} (t : PredTrans (.arg σ ps) α) :
  (t.popArg s).apply Q = t.apply (fun a s => Q.1 (a, s), Q.2) s := rfl

@[simp]
def PredTrans.popExcept_apply {ps} {Q : PostCond (Except ε α) ps} (t : PredTrans (.except ε ps) α) :
  (t.popExcept).apply Q = t.apply (fun a => Q.1 (.ok a), fun e => Q.1 (.error e), Q.2) := rfl

@[simp]
def PredTrans.withReader_apply {ps} {Q : PostCond α (.arg ρ ps)} (f : ρ → ρ) (t : PredTrans (.arg ρ ps) α) :
  (PredTrans.withReader f t).apply Q = fun r => t.apply (fun a _ => Q.1 a r, Q.2) (f r) := rfl

instance PredTrans.instMonadMorphismPushArg : MonadMorphism (StateT σ (PredTrans ps)) (PredTrans (.arg σ ps)) (PredTrans.pushArg) where
  pure_pure := by intros; rfl
  bind_bind := by intros; rfl

instance PredTrans.instMonadMorphismPopArg : MonadMorphism (PredTrans (.arg σ ps)) (StateT σ (PredTrans ps)) (PredTrans.popArg) where
  pure_pure := by intros; rfl
  bind_bind := by intros; rfl

@[simp]
theorem PredTrans.pushArg_popArg : pushArg (popArg x) = x := rfl

@[simp]
theorem PredTrans.popArg_pushArg : popArg (pushArg f) = f := rfl

-- Just a reminder for me that the following would not hold for a suitable defn of pushReader and popReader:
--theorem PredTrans.pushReader_popReader : pushReader (popReader x) = x := sorry
--  goal: x.apply (fun a x => Q.1 a x✝, Q.2) x✝ = x.apply Q x✝

instance PredTrans.instMonadMorphismPushExcept : MonadMorphism (ExceptT ε (PredTrans ps)) (PredTrans (.except ε ps)) (PredTrans.pushExcept) where
  pure_pure := by intros; rfl
  bind_bind := by
    intro _ _ x f
    ext Q
    simp only [pushExcept, Bind.bind, ExceptT.bind, ExceptT.mk, bind, ExceptT.bindCont]
    congr
    ext x
    cases x <;> simp

instance PredTrans.instMonadMorphismPopExcept : MonadMorphism (PredTrans (.except ε ps)) (ExceptT ε (PredTrans ps)) (PredTrans.popExcept) where
  pure_pure := by intros; rfl
  bind_bind := by intros; rfl

@[simp]
theorem PredTrans.pushExcept_popExcept : pushExcept (popExcept x) = x := rfl

@[simp]
theorem PredTrans.popExcept_pushExcept : popExcept (pushExcept x) = x := by
  ext Q
  simp only [ExceptT.run, popExcept, pushExcept]
  congr
  ext x
  cases x <;> simp
