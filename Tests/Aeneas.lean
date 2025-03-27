import MPL

open MPL

inductive Error where
   | assertionFailure: Error
   | integerOverflow: Error
   | divisionByZero: Error
   | arrayOutOfBounds: Error
   | maximumSizeExceeded: Error
   | panic: Error
   | undef: Error
deriving Repr, BEq

open Error

inductive Result (α : Type u) where
  | ok (v: α): Result α
  | fail (e: Error): Result α
  | div
deriving Repr, BEq

instance : Monad Result where
  pure x := .ok x
  bind x f := match x with
  | .ok v => f v
  | .fail e => .fail e
  | .div => .div

instance : LawfulMonad Result := sorry

instance Result.instWP : WP Result (.except Error .pure) where
  wp x := match x with
  | .ok v => wp⟦pure v : Except Error _⟧
  | .fail e => wp⟦throw e : Except Error _⟧
  | .div => PredTrans.top -- const False

instance : WPMonad Result (.except Error .pure) where
  pure_pure := by intros; simp[wp]
  bind_bind x f := by
    intros
    simp[Result.instWP, bind]
    ext Q
    cases x <;> simp[PredTrans.bind, PredTrans.top, PredTrans.const]; xwp
    sorry -- Sigh; need to remove the redundant Monad (Except ε) instance
          -- which is not defeq to Monad (ExceptT ε Id)

/-- Kinds of unsigned integers -/
inductive UScalarTy where
| Usize
| U8
| U16
| U32
| U64
| U128

def UScalarTy.numBits (ty : UScalarTy) : Nat :=
  match ty with
  | Usize => System.Platform.numBits
  | U8 => 8
  | U16 => 16
  | U32 => 32
  | U64 => 64
  | U128 => 128

/-- Signed integer -/
structure UScalar (ty : UScalarTy) where
  /- The internal representation is a bit-vector -/
  bv : BitVec ty.numBits
deriving Repr, BEq, DecidableEq

def UScalar.val {ty} (x : UScalar ty) : ℕ := x.bv.toNat

def UScalar.ofNatCore {ty : UScalarTy} (x : Nat) (_ : x < 2^ty.numBits) : UScalar ty :=
  { bv := BitVec.ofNat _ x }

instance (ty : UScalarTy) : CoeOut (UScalar ty) Nat where
  coe := λ v => v.val

def UScalar.tryMk (ty : UScalarTy) (x : Nat) : Result (UScalar ty) :=
  sorry

def UScalar.add {ty : UScalarTy} (x y : UScalar ty) : Result (UScalar ty) :=
  UScalar.tryMk ty (x.val + y.val)

instance {ty} : HAdd (UScalar ty) (UScalar ty) (Result (UScalar ty)) where
  hAdd x y := UScalar.add x y

irreducible_def UScalar.max (ty : UScalarTy) : Nat := 2^ty.numBits-1

theorem UScalar.add_spec {ty} {x y : UScalar ty}
  (hmax : ↑x + ↑y ≤ UScalar.max ty) :
  ∃ z, x + y = Result.ok z ∧ (↑z : Nat) = ↑x + ↑y := sorry

abbrev U32 := UScalar .U32
abbrev U32.max   : Nat := UScalar.max .U32

theorem U32.add_spec {x y : U32} (hmax : x.val + y.val ≤ U32.max) :
  ∃ z, x + y = Result.ok z ∧ (↑z : Nat) = ↑x + ↑y :=
  UScalar.add_spec sorry -- (by scalar_tac)

abbrev PCond (α : Type) := PostCond α (PredShape.except Error PredShape.pure)

theorem U32.add_spec' {x y : U32} {Q : PCond U32} (hmax : ↑x + ↑y ≤ U32.max):
  ⦃Q.1 (UScalar.ofNatCore (↑x + ↑y) sorry)⦄ (x + y) ⦃Q⦄ := by
    xstart
    intro h
    have ⟨z, ⟨hxy, hz⟩⟩ := U32.add_spec hmax
    simp[hxy, hz.symm, wp]
    sorry -- show Q.1 z ↔ Q.1 (ofNatCore z.val ⋯)

@[simp]
theorem UScalar.ofNatCore_val_eq : (ofNatCore x h).val = x := sorry

def mul2_add1 (x : U32) : Result U32 :=
  do
  let i ← x + x
  i + (UScalar.ofNatCore 1 sorry : U32)

theorem mul2_add1_spec' (x : U32) (h : 2 * x.val + 1 ≤ U32.max)
  : ⦃Q.1 (UScalar.ofNatCore (2 * ↑x + (1 : Nat)) sorry)⦄ (mul2_add1 x) ⦃Q⦄ := by
  rw[mul2_add1]
  xstart
  intro h
  xapp U32.add_spec' (by omega)
  xapp U32.add_spec' (by simp; omega)
  simp +arith [h]

-- for more `progress` like automation, we can register a wp transformer:
@[wp_simp]
theorem U32.add_apply {x y : U32} {Q : PCond U32} :
    wp⟦x + y⟧.apply Q =
    if h : ↑x + ↑y ≤ U32.max
    then Q.1 (UScalar.ofNatCore (↑x + ↑y) sorry) -- massage h
    else Q.2.1 integerOverflow := by
    split
    next h =>
      have ⟨z, ⟨hxy, hz⟩⟩ := U32.add_spec h
      simp[hxy, hz.symm, wp]
      sorry -- show Q.1 z ↔ Q.1 (ofNatCore z.val ⋯)
    next h =>
      simp[wp,HAdd.hAdd,UScalar.add]
      have : ¬x.val + y.val ≤ U32.max → UScalar.tryMk .U32 (Add.add x.val y.val) = Result.fail integerOverflow :=
        sorry -- by definition of tryMk
      simp[this h]
      xwp
      -- goddamn Monad (Except ε)!!
      sorry

theorem mul2_add1_apply (x : U32) (h : 2 * x.val + 1 ≤ U32.max)
  : wp⟦mul2_add1 x⟧.apply Q = Q.1 (UScalar.ofNatCore (2 * ↑x + (1 : Nat)) sorry) := by
  rw[mul2_add1]
  xwp
  simp +arith +contextual [h]
  omega
