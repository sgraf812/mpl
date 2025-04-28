import MPL

namespace MPL.VSTTE2010

namespace MaxAndSum

def max_and_sum (xs : Array Nat) : Idd (Nat × Nat) := do
  let mut max := 0
  let mut sum := 0
  for h : i in [0:xs.size] do
    sum := sum + xs[i]
    if xs[i] > max then
      max := xs[i]
  return (max, sum)

theorem max_and_sum_spec (xs : Array Nat) :
    ⦃⌜∀ i, (h : i < xs.size) → xs[i] ≥ 0⌝⦄ max_and_sum xs ⦃⇓ (m, s) => s ≤ m * xs.size ⦄ := by
  unfold max_and_sum
  mintro ⌜h⌝
  mwp
  mspec (Specs.forIn_list (⇓ ((m, s), xs) => s ≤ m * xs.pref.length) ?step)
  case step =>
    mwp
    sorry

end MaxAndSum
