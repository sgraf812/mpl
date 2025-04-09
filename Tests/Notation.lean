import MPL.SProp.Notation

open MPL

variable
  (φ : Prop)
  (P Q R : SProp [Nat,Char,Bool])
  (Ψ : Nat → SProp [Nat, Char, Bool])
  (Φ : Nat → Nat → SProp [Nat, Char, Bool])

/-- info: P ⊢ₛ Q : Prop -/
#guard_msgs in
#check P ⊢ₛ Q

/-- info: P ⊢ₛ Q : Prop -/
#guard_msgs in
#check P ⊢ₛ Q

/-- info: P ⊣⊢ₛ Q : Prop -/
#guard_msgs in
#check P ⊣⊢ₛ Q


/-- info: ⌜φ⌝ : SProp ?m.716 -/
#guard_msgs in
#check ⌜φ⌝

/-- info: ⌜7 + ‹Nat›ₛ = if ‹Bool›ₛ = true then 13 else 7⌝ : SProp [Nat, Char, Bool] -/
#guard_msgs in
#check (⌜7 + ‹Nat›ₛ = if ‹Bool›ₛ then 13 else 7⌝ : SProp [Nat,Char,Bool])

private abbrev theChar : SVal [Nat,Char,Bool] Char := fun _ c _ => c
/-- info: ⌜#theChar = 'a'⌝ : SProp [Nat, Char, Bool] -/
#guard_msgs in
#check ⌜#theChar = 'a'⌝


/-- info: sprop(P ∧ Q) : SProp [Nat, Char, Bool] -/
#guard_msgs in
#check sprop(P ∧ Q)

/-- info: sprop(P ∧ Q ∧ R) : SProp [Nat, Char, Bool] -/
#guard_msgs in
#check sprop(P ∧ (Q ∧ R))

/-- info: sprop(P ∨ Q) : SProp [Nat, Char, Bool] -/
#guard_msgs in
#check sprop(P ∨ Q)

/-- info: sprop(P ∨ Q ∨ R) : SProp [Nat, Char, Bool] -/
#guard_msgs in
#check sprop(P ∨ (Q ∨ R))

/-- info: sprop(¬P) : SProp [Nat, Char, Bool] -/
#guard_msgs in
#check sprop(¬ P)

/-- info: sprop(¬(P ∨ Q)) : SProp [Nat, Char, Bool] -/
#guard_msgs in
#check sprop(¬ (P ∨ Q))


/-- info: sprop(P → Q) : SProp [Nat, Char, Bool] -/
#guard_msgs in
#check sprop(P → Q)

/-- info: sprop(P → Q → R) : SProp [Nat, Char, Bool] -/
#guard_msgs in
#check sprop(P → (Q → R))

/-- info: sprop(P ∧ Q → R) : SProp [Nat, Char, Bool] -/
#guard_msgs in
#check sprop((P ∧ Q) → R)

/-- info: sprop(P → Q ∧ R) : SProp [Nat, Char, Bool] -/
#guard_msgs in
#check sprop(P → (Q ∧ R))


/-- info: sprop(P ↔ Q) : SProp [Nat, Char, Bool] -/
#guard_msgs in
#check sprop(P ↔ Q)

/-- info: sprop(P ∧ Q ↔ Q ∧ P) : SProp [Nat, Char, Bool] -/
#guard_msgs in
#check sprop((P ∧ Q) ↔ (Q ∧ P))


/-- info: ∀ (x : Nat), x = 0 : Prop -/
#guard_msgs in
#check ∀ (x : Nat), x = 0

/-- info: sprop(∀ x, Ψ x) : SProp [Nat, Char, Bool] -/
#guard_msgs in
#check sprop(∀ x, Ψ x)

/-- info: sprop(∀ x, Ψ x) : SProp [Nat, Char, Bool] -/
#guard_msgs in
#check sprop(∀ (x : Nat), Ψ x)

/-- info: sprop(∀ x, ∀ y, Φ x y) : SProp [Nat, Char, Bool] -/
#guard_msgs in
#check sprop(∀ x y, Φ x y)

/-- info: sprop(∀ x, ∀ y, Φ x y) : SProp [Nat, Char, Bool] -/
#guard_msgs in
#check sprop(∀ (x : Nat) (y : Nat), Φ x y)

/-- info: sprop(∀ x, ∀ y, Φ x y) : SProp [Nat, Char, Bool] -/
#guard_msgs in
#check sprop(∀ (x y : Nat), Φ x y)


/-- info: sprop(∃ x, Ψ x) : SProp [Nat, Char, Bool] -/
#guard_msgs in
#check sprop(∃ x, Ψ x)

/-- info: sprop(∃ x, Ψ x) : SProp [Nat, Char, Bool] -/
#guard_msgs in
#check sprop(∃ (x : Nat), Ψ x)

/-- info: sprop(∃ x, ∃ y, Φ x y) : SProp [Nat, Char, Bool] -/
#guard_msgs in
#check sprop(∃ x y, Φ x y)

/-- info: sprop(∃ x, ∃ y, Φ x y) : SProp [Nat, Char, Bool] -/
#guard_msgs in
#check sprop(∃ (x : Nat) (y : Nat), Φ x y)

/-- info: sprop(∃ x, ∃ y, Φ x y) : SProp [Nat, Char, Bool] -/
#guard_msgs in
#check sprop(∃ (x y : Nat), Φ x y)


/--
info: if true = true then
  match (1, 2) with
  | (x, y) => Φ x y
else ⌜False⌝ : SProp [Nat, Char, Bool]
-/
#guard_msgs in
#check sprop(if true then term(match (1,2) with | (x,y) => Φ x y) else ⌜False⌝)

/-- info: Ψ (1 + 1) : SProp [Nat, Char, Bool] -/
#guard_msgs in
#check sprop(Ψ (1 + 1))
