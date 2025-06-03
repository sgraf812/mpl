import MPL
import MPL.Experimental

set_option grind.warning false

open MPL

--
-- Bird's eye view
--

abbrev fib_spec : Nat → Nat
| 0 => 0
| 1 => 1
| n+2 => fib_spec n + fib_spec (n+1)

-- Extended `def` syntax:
def fib_impl (n : Nat) : Idd Nat
  ensures r => r = fib_spec n
:= do
  if n = 0 then return 0
  let mut a := 0
  let mut b := 1
  invariant xs => a = fib_spec xs.rpref.length ∧ b = fib_spec (xs.rpref.length + 1)
  for _ in [1:n] do
    let a' := a
    a := b
    b := a' + b
  return b

-- intrinsic, automated proof:
#check fib_impl.spec

theorem fib_correct {n} : (fib_impl n).run = fib_spec n := by
  generalize h : (fib_impl n).run = x
  apply Idd.by_wp h
  apply fib_impl.spec n True.intro


-- extrinsic, manual proof:
theorem fib_triple : ⦃⌜True⌝⦄ fib_impl n ⦃⇓ r => r = fib_spec n⦄ := by
  unfold fib_impl
  dsimp
  mintro _
  if h : n = 0 then simp [h] else
  simp only [h]
  mwp
  mspec Specs.forIn_list (⇓ (⟨a, b⟩, xs) => a = fib_spec xs.rpref.length ∧ b = fib_spec (xs.rpref.length + 1)) ?step
  case step => dsimp; intros; mintro _; mwp; simp_all
  simp_all [Nat.sub_one_add_one]

--
-- Compositional proofs using Hoare triple specifications
--

abbrev AppState := Nat

def mkFreshNat : StateM AppState Nat
  forall (n : Nat)
  requires s => ⌜s = n⌝
  ensures r s => ⌜r = n ∧ s = n + 1⌝
:= do
  let n ← get
  set (n+1)
  pure n

#check mkFreshNat.spec

noncomputable def mkFreshPair : StateM AppState (Nat × Nat) := do
  let a ← mkFreshNat
  let b ← mkFreshNat
  pure (a, b)

@[spec]
theorem mkFreshPair_spec :
  ⦃⌜True⌝⦄
  mkFreshPair
  ⦃⇓ (a, b) => ⌜a ≠ b⌝⦄ := by
  unfold mkFreshPair
  mintro - ∀s
  mspec mkFreshNat.spec
  mintro ∀s
  mcases h with ⌜h₁⌝
  mspec mkFreshNat.spec
  mintro ∀s
  mcases h with ⌜h₂⌝
  simp_all [h₁, h₂]



--
-- Proof mode
--

abbrev M := StateT Nat (StateT Char (StateT Bool (StateT String Idd)))
axiom op : Nat → M Nat
noncomputable def prog (n : Nat) : M Nat := do
  let a ← op n
  let b ← op a
  let c ← op b
  return (a + b + c)

axiom isValid : Nat → Char → Bool → String → Prop

axiom op.spec {n} : ⦃isValid⦄ op n ⦃⇓r => ⌜r > 42⌝ ∧ isValid⦄

theorem prog.spec : ⦃isValid⦄ prog n ⦃⇓r => ⌜r > 100⌝ ∧ isValid⦄ := by
  -- This is an example for the (emulated) proof experience without a proof mode.
  -- Note that after every application of a spec, we need to reintroduce all state variables.
  unfold prog
  unfold Triple
  change ∀ a b c d, isValid a b c d → _
  intro a b c d h
  set_option trace.mpl.tactics.spec true in
  mstart; mspec op.spec; mstop
  intro a b c d ⟨hr₁, hvalid⟩
  mstart; mspec op.spec; mstop
  intro a b c d ⟨hr₂, hvalid⟩
  mstart; mspec op.spec; mstop
  intro a b c d ⟨hr₃, hvalid⟩
  mstart; mspec; mstop
  simp_all
  omega

theorem prog.spec' : ⦃isValid⦄ prog n ⦃⇓r => ⌜r > 100⌝ ∧ isValid⦄ := by
  unfold prog
  mintro h
  mspec op.spec
  mcases h with ⟨hr₁, h⟩
  mspec op.spec
  mcases h with ⟨hr₂, h⟩
  mspec op.spec
  mcases h with ⟨hr₃, h⟩
  mspec
  mrefine ⟨?_, h⟩
  mpure_intro
  omega

--
-- mspec
--

example [WP m ps] (x : m α)
   (hspec : ⦃P⦄ x ⦃Q⦄)
   (hpre : P' ⊢ₛ P)
   (hpost : Q ⊢ₚ Q')
   : P' ⊢ₛ wp⟦x⟧ Q' := by
  mintro h
  mspec hspec
  case pre1 => exact hpre
  case post => exact hpost

example [WP m ps] (x : m α) (Q : α → Assertion ps)
   (hspec : ⦃P⦄ x ⦃⇓ v => Q v⦄)
   (hpre : P' ⊢ₛ P)
   (hpost : ∀ v, Q v ⊢ₛ Q'.1 v)
   : P' ⊢ₛ wp⟦x⟧ Q' := by
  mintro h
  mspec hspec
  case pre1 => exact hpre
  case post.success => exact hpost r

#check Specs.forIn_list

--
-- Verification conditions
--

theorem fib_impl_vcs
    (Q : Nat → PostCond Nat PostShape.pure)
    (I : (n : Nat) → (_ : ¬n = 0) →
      PostCond (MProd Nat Nat × List.Zipper [1:n].toList) PostShape.pure)
    (ret : (Q 0).1 0)
    (loop_pre : ∀ n (hn : ¬n = 0), (I n hn).1 (⟨0, 1⟩, List.Zipper.begin _))
    (loop_post : ∀ n (hn : ¬n = 0) r, (I n hn).1 (r, List.Zipper.end _) ⊢ₛ (Q n).1 r.snd)
    (loop_step : ∀ n (hn : ¬n = 0) r rpref x suff (h : [1:n].toList = rpref.reverse ++ x :: suff),
                  (I n hn).1 (r, ⟨rpref, x::suff, by simp[h]⟩) ⊢ₛ (I n hn).1 (⟨r.2, r.1+r.2⟩, ⟨x::rpref, suff, by simp[h]⟩))
    : wp⟦fib_impl n⟧ (Q n) := by
  apply fib_impl.fun_cases n _ ?case1 ?case2
  case case1 => unfold fib_impl; intro h; mstart; simp only [*, reduceIte]; mspec
  case case2 =>
  intro hn
  unfold fib_impl
  simp only [*, reduceIte]
  mstart
  mspec
  mspec
  mspec
  case inv => exact I n hn
  case pre1 => mpure_intro; apply_rules [loop_pre]
  case post.success => mspec; mpure_intro; apply_rules [loop_post]
  case step =>
    intros;
    mintro _;
    mspec
    mspec
    mpure_intro
    apply_rules [loop_step]






-- Recall from above:
theorem fib_triple' : ⦃⌜True⌝⦄ fib_impl n ⦃⇓ r => r = fib_spec n⦄ := by
  unfold fib_impl
  dsimp
  mintro _
  if h : n = 0 then simp [h] else
  simp only [h]
  mwp
  mspec Specs.forIn_list (⇓ (⟨a, b⟩, xs) => a = fib_spec xs.rpref.length ∧ b = fib_spec (xs.rpref.length + 1)) ?step
  case step => dsimp; intros; mintro _; mwp; simp_all
  simp_all [Nat.sub_one_add_one]

-- Now decompose:

theorem fib_triple_vcs : ⦃⌜True⌝⦄ fib_impl n ⦃⇓ r => r = fib_spec n⦄ := by
  intro _
  apply fib_impl_vcs
  case I => intro n hn; exact ⇓ (⟨a, b⟩, xs) =>
    a = fib_spec xs.rpref.length ∧ b = fib_spec (xs.rpref.length + 1)
  case ret => rfl
  case loop_pre => simp
  case loop_post => simp_all[Nat.sub_one_add_one]
  case loop_step => simp_all

-- mvcgen gives us `fib_impl_vcs`. In practice, we don't bother extracting a theorem for it and
-- use `mvcgen` directly:

theorem fib_triple_vcs' : ⦃⌜True⌝⦄ fib_impl n ⦃⇓ r => r = fib_spec n⦄ := by
  mvcgen [fib_impl]
  case inv => exact ⇓ (⟨a, b⟩, xs) =>
    a = fib_spec xs.rpref.length ∧ b = fib_spec (xs.rpref.length + 1)
  all_goals simp_all [Nat.sub_one_add_one]

theorem fib_impl_vcs'
    (Q : Nat → PostCond Nat PostShape.pure)
    (I : (n : Nat) → (_ : ¬n = 0) →
      PostCond (MProd Nat Nat × List.Zipper [1:n].toList) PostShape.pure)
    (ret : (Q 0).1 0)
    (loop_pre : ∀ n (hn : ¬n = 0), (I n hn).1 (⟨0, 1⟩, List.Zipper.begin _))
    (loop_post : ∀ n (hn : ¬n = 0) r, (I n hn).1 (r, List.Zipper.end _) ⊢ₛ (Q n).1 r.snd)
    (loop_step : ∀ n (hn : ¬n = 0) r rpref x suff (h : [1:n].toList = rpref.reverse ++ x :: suff),
                  (I n hn).1 (r, ⟨rpref, x::suff, by simp[h]⟩) ⊢ₛ (I n hn).1 (⟨r.2, r.1+r.2⟩, ⟨x::rpref, suff, by simp[h]⟩))
    : wp⟦fib_impl n⟧ (Q n) := by
  mvcgen [fib_impl]
  case inv => apply_rules [I]
  all_goals simp_all


















--
-- A bit more complex and realistic example:
-- Serialization/deserialization of a file format.
--

structure File where
  bytes : Array UInt8
  pos : Fin (bytes.size + 1)

inductive FileError where
  | invalidPos
  | invalidFormat
  | eof

abbrev FileM := EStateM FileError File

def FileM.read (nbytes : Nat) : FileM (Vector UInt8 nbytes) := do
  let f ← get
  let mut ret := Vector.replicate nbytes default
  let mut pos := f.pos
  for h₁ : i in [:nbytes] do
    if h₂ : pos < f.bytes.size then
      ret := ret.set i f.bytes[pos]
      pos := pos.succ.castLT (by simp[h₂])
    else
      throw FileError.eof
  set { f with pos := pos }
  return ret

theorem range_elim : List.range' s n = xs ++ i :: ys → i = s + xs.length := by
  intro h
  induction xs generalizing s n
  case nil => cases n <;> simp_all[List.range']
  case cons head tail ih =>
    cases n <;> simp[List.range'] at h
    have := ih h.2
    simp[ih h.2]
    omega

def canRead (n : Nat) (f : File) : Prop :=
  f.pos + n ≤ f.bytes.size

def hasRead {n : Nat} (v : Vector UInt8 n) (oldF newF : File) : Prop :=
  oldF.bytes = newF.bytes ∧ oldF.pos + n = newF.pos  ∧ oldF.bytes.extract oldF.pos newF.pos = v.toArray

theorem read_spec :
  ⦃fun f' => canRead n f' ∧ f' = f⦄ FileM.read n ⦃⇓ v => hasRead v f⦄ := by
  mintro h ∀f'
  mpure h
  have ⟨hread, hfile⟩ := h
  subst hfile
  unfold FileM.read
  mwp
  mspec (Specs.forIn'_list ?inv ?step)
  case inv => exact ⇓ (⟨pos, buf⟩, xs) =>
    ⌜pos = f'.pos + xs.pref.length ∧ pos + xs.suff.length ≤ f'.bytes.size
    ∧ f'.bytes.extract f'.pos pos = buf.toArray.take xs.pref.length⌝
  case pre1 => intro hread; simp_all[canRead]; omega
  case step =>
    intro ⟨pos, buf⟩ pref i hi suff hsuff
    have := range_elim hsuff
    simp at this
    subst_vars
    mintro ⌜hinv⌝
    simp at hinv
    mwp
    split
    · mpure_intro
      simp +arith [hinv]
      sorry -- pure proof about offset arithmetic and Array.extract
    · simp_all
      omega
  case post.except.handle => simp
  mintro ∀f
  simp_all [hasRead]
