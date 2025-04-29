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
  mspec (Specs.forIn'_list (⇓ (⟨m, s⟩, xs) => s ≤ m * xs.rpref.length) ?step)
  case step =>
    intro ⟨m, s⟩ pref x hx suff hzipper
    mintro ⌜hsum⌝
    mwp
    split
    next h =>
      -- it would be great if grind would solve this
      simp_all
      rw[Nat.left_distrib]
      simp
      apply Nat.le_trans hsum
      apply Nat.mul_le_mul_right
      omega
    next h =>
      simp_all
      rw[Nat.left_distrib]
      omega
  simp

end MaxAndSum

namespace InvertInjection

def invert_injection (xs : Vector Nat N) (h : ∀ i, (h : i < N) → xs[i] < N) : Idd (Vector Nat N) := do
  let mut ys := xs
  for h' : i in [0:N] do
    have h' : xs[i] < N := h i (by get_elem_tactic)
    ys := ys.set xs[i] i
  return ys

def invert_injection' (xs : Vector Nat N) : Idd (Vector Nat N) := do
  let mut ys := xs
  for i in [0:ys.size] do
    ys := ys.set! xs[i]! i
  return ys

@[grind]
theorem range_elim : List.range' s n = xs ++ i :: ys → i = s + xs.length := by
  intro h
  induction xs generalizing s n
  case nil => cases n <;> simp_all[List.range']
  case cons head tail ih =>
    cases n <;> simp[List.range'] at h
    have := ih h.2
    simp[ih h.2]
    omega

theorem invert_injection_spec (xs : Array Nat)
    (h : ∀ i, (h : i < xs.size) → xs[i] < xs.size) :
    ⦃⌜True⌝⦄
    invert_injection' xs
    ⦃⇓ ys => ∃ (h₁ : ys.size = xs.size), ∀ i, (h₂ : i < xs.size) → ys[xs[i]]'(h₁ ▸ h i h₂) = i ⦄ := by
  unfold invert_injection'
  mintro -
  mwp
  mspec (Specs.forIn_list ?inv ?step)
  case inv => exact (⇓ (ys, is) =>
    ∃ (h₁ : ys.size = xs.size), ∀ i, (h₂ : i < is.rpref.length) →
      have h₃ : xs.size = is.rpref.length + is.suff.length := by
        calc xs.size
          _ = (List.range' 0 (xs.size - 0) 1).length := by simp
          _ = (is.pref ++ is.suff).length := by simp only [is.property.symm]
          _ = is.rpref.length + is.suff.length := by simp
      have h₃ : is.rpref.length ≤ xs.size := by simp[h₃]
      have h₂ : i < xs.size := Nat.lt_of_lt_of_le h₂ h₃
      ys[xs[i]]'(h₁ ▸ h i h₂) = i)
  case pre => simp
  case step =>
    intro ys rpref i suff hzipper
    mintro ⌜h⌝
    simp at h
    rcases h with ⟨h₁, h₂⟩
    mwp
    simp_all only [PostShape.args, SVal.curry_nil, Array.set!_eq_setIfInBounds, List.length_cons,
      SPred.forall_nil, SPred.exists_nil, Array.size_setIfInBounds, exists_true_left,
      SPred.entails_nil, forall_const]
    intro j h₃
    if h₄ : j = rpref.length
    then
      simp[range_elim hzipper, h₄, Array.getElem_setIfInBounds_self, Array.getElem!_eq_setIfInBounds]
    have := h₂ j h₃

end InvertInjection
