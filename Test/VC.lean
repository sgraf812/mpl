import MPL
import MPL.ProofMode.Tactics.VCGen
import Test.Code

namespace MPL.Test.VC

open MPL.Test.Code

theorem fib_triple : ⦃⌜True⌝⦄ fib_impl n ⦃⇓ r => r = fib_spec n⦄ := by
  unfold fib_impl
  mvcgen
  case inv => exact ⇓ (⟨a, b⟩, xs) =>
    a = fib_spec xs.rpref.length ∧ b = fib_spec (xs.rpref.length + 1)
  all_goals simp_all +zetaDelta [Nat.sub_one_add_one]

-- TODO: Use strongest post
theorem ifs_triple : ⦃⌜True⌝⦄ ifs n ⦃⇓ r => ⌜r > 0⌝⦄ := by
  unfold ifs
  mvcgen <;> simp +zetaDelta

private abbrev fst : SVal (AppState::σs) Nat := fun s => SVal.pure s.1
private abbrev snd : SVal (AppState::σs) Nat := fun s => SVal.pure s.2

--set_option trace.Meta.whnf true in
@[spec]
theorem mkFreshNat_spec [Monad m] [WPMonad m sh] :
  ⦃⌜#fst = n ∧ #snd = o⌝⦄
  (mkFreshNat : StateT AppState m Nat)
  ⦃⇓ r => ⌜r = n ∧ #fst = n + 1 ∧ #snd = o⌝⦄ := by
  unfold mkFreshNat
  mvcgen <;> simp_all

@[spec]
theorem mkFreshNat_spec' [Monad m] [WPMonad m sh] :
  ⦃⌜#fst = n ∧ #snd = o⌝⦄
  (mkFreshNat : StateM AppState Nat)
  ⦃⇓ r => ⌜r = n ∧ #fst = n + 1 ∧ #snd = o⌝⦄ := by
  unfold mkFreshNat
  mvcgen <;> simp_all

theorem mkFreshPair_triple : ⦃⌜True⌝⦄ mkFreshPair ⦃⇓ (a, b) => ⌜a ≠ b⌝⦄ := by
  unfold mkFreshPair
  mvcgen
