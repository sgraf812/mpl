import MPL.SPred.Notation

open MPL

variable
  (φ : Prop)
  (P Q R : SPred [Nat,Char,Bool])
  (Ψ : Nat → SPred [Nat, Char, Bool])
  (Φ : Nat → Nat → SPred [Nat, Char, Bool])

/-- info: P ⊢ₛ Q : Prop -/
#guard_msgs in
#check P ⊢ₛ Q

/-- info: P ⊢ₛ Q : Prop -/
#guard_msgs in
#check P ⊢ₛ Q

/-- info: P ⊣⊢ₛ Q : Prop -/
#guard_msgs in
#check P ⊣⊢ₛ Q


/-- info: ⌜φ⌝ : SPred ?m.716 -/
#guard_msgs in
#check ⌜φ⌝

/-- info: ⌜7 + ‹Nat›ₛ = if ‹Bool›ₛ = true then 13 else 7⌝ : SPred [Nat, Char, Bool] -/
#guard_msgs in
#check (⌜7 + ‹Nat›ₛ = if ‹Bool›ₛ then 13 else 7⌝ : SPred [Nat,Char,Bool])

private abbrev theChar : SVal [Nat,Char,Bool] Char := fun _ c _ => c
/-- info: ⌜#theChar = 'a'⌝ : SPred [Nat, Char, Bool] -/
#guard_msgs in
#check ⌜#theChar = 'a'⌝


/-- info: SPred(P ∧ Q) : SPred [Nat, Char, Bool] -/
#guard_msgs in
#check SPred(P ∧ Q)

/-- info: SPred(P ∧ Q ∧ R) : SPred [Nat, Char, Bool] -/
#guard_msgs in
#check SPred(P ∧ (Q ∧ R))

/-- info: SPred(P ∨ Q) : SPred [Nat, Char, Bool] -/
#guard_msgs in
#check SPred(P ∨ Q)

/-- info: SPred(P ∨ Q ∨ R) : SPred [Nat, Char, Bool] -/
#guard_msgs in
#check SPred(P ∨ (Q ∨ R))

/-- info: SPred(¬P) : SPred [Nat, Char, Bool] -/
#guard_msgs in
#check SPred(¬ P)

/-- info: SPred(¬(P ∨ Q)) : SPred [Nat, Char, Bool] -/
#guard_msgs in
#check SPred(¬ (P ∨ Q))


/-- info: SPred(P → Q) : SPred [Nat, Char, Bool] -/
#guard_msgs in
#check SPred(P → Q)

/-- info: SPred(P → Q → R) : SPred [Nat, Char, Bool] -/
#guard_msgs in
#check SPred(P → (Q → R))

/-- info: SPred(P ∧ Q → R) : SPred [Nat, Char, Bool] -/
#guard_msgs in
#check SPred((P ∧ Q) → R)

/-- info: SPred(P → Q ∧ R) : SPred [Nat, Char, Bool] -/
#guard_msgs in
#check SPred(P → (Q ∧ R))


/-- info: SPred(P ↔ Q) : SPred [Nat, Char, Bool] -/
#guard_msgs in
#check SPred(P ↔ Q)

/-- info: SPred(P ∧ Q ↔ Q ∧ P) : SPred [Nat, Char, Bool] -/
#guard_msgs in
#check SPred((P ∧ Q) ↔ (Q ∧ P))


/-- info: ∀ (x : Nat), x = 0 : Prop -/
#guard_msgs in
#check ∀ (x : Nat), x = 0

/-- info: SPred(∀ x, Ψ x) : SPred [Nat, Char, Bool] -/
#guard_msgs in
#check SPred(∀ x, Ψ x)

/-- info: SPred(∀ x, Ψ x) : SPred [Nat, Char, Bool] -/
#guard_msgs in
#check SPred(∀ (x : Nat), Ψ x)

/-- info: SPred(∀ x, ∀ y, Φ x y) : SPred [Nat, Char, Bool] -/
#guard_msgs in
#check SPred(∀ x y, Φ x y)

/-- info: SPred(∀ x, ∀ y, Φ x y) : SPred [Nat, Char, Bool] -/
#guard_msgs in
#check SPred(∀ (x : Nat) (y : Nat), Φ x y)

/-- info: SPred(∀ x, ∀ y, Φ x y) : SPred [Nat, Char, Bool] -/
#guard_msgs in
#check SPred(∀ (x y : Nat), Φ x y)


/-- info: SPred(∃ x, Ψ x) : SPred [Nat, Char, Bool] -/
#guard_msgs in
#check SPred(∃ x, Ψ x)

/-- info: SPred(∃ x, Ψ x) : SPred [Nat, Char, Bool] -/
#guard_msgs in
#check SPred(∃ (x : Nat), Ψ x)

/-- info: SPred(∃ x, ∃ y, Φ x y) : SPred [Nat, Char, Bool] -/
#guard_msgs in
#check SPred(∃ x y, Φ x y)

/-- info: SPred(∃ x, ∃ y, Φ x y) : SPred [Nat, Char, Bool] -/
#guard_msgs in
#check SPred(∃ (x : Nat) (y : Nat), Φ x y)

/-- info: SPred(∃ x, ∃ y, Φ x y) : SPred [Nat, Char, Bool] -/
#guard_msgs in
#check SPred(∃ (x y : Nat), Φ x y)


/--
info: if true = true then
  match (1, 2) with
  | (x, y) => Φ x y
else ⌜False⌝ : SPred [Nat, Char, Bool]
-/
#guard_msgs in
#check SPred(if true then term(match (1,2) with | (x,y) => Φ x y) else ⌜False⌝)

/-- info: Ψ (1 + 1) : SPred [Nat, Char, Bool] -/
#guard_msgs in
#check SPred(Ψ (1 + 1))
