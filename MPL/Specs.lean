/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
import MPL.Triple
import MPL.SpecAttr

/-!
# Hoare triple specifications for select functions

This module contains Hoare triple specifications for some functions in Core.
-/

namespace Std.Range

abbrev toList (r : Std.Range) : List Nat :=
  List.range' r.start ((r.stop - r.start + r.step - 1) / r.step) r.step

end Std.Range

namespace MPL

namespace List

@[ext]
structure Zipper {α : Type u} (l : List α) : Type u where
  rpref : List α
  suff : List α
  property : rpref.reverse ++ suff = l

abbrev Zipper.pref {α} {l : List α} (s : List.Zipper l) : List α := s.rpref.reverse

abbrev Zipper.begin (l : List α) : Zipper l := ⟨[],l,rfl⟩
abbrev Zipper.end (l : List α) : Zipper l := ⟨l.reverse,[],by simp⟩
abbrev Zipper.tail (s : Zipper l) (h : s.suff = hd::tl) : Zipper l :=
  { rpref := hd::s.rpref, suff := tl, property := by simp [s.property, ←h] }

@[simp]
theorem Zipper.begin_eq_end_iff_nil {l : List α} : Zipper.begin l = Zipper.end l ↔ l = [] := by
  constructor <;> simp [begin, Zipper.end]

@[simp]
theorem Zipper.nil_begin_eq_end : Zipper.begin ([] : List α) = Zipper.end ([] : List α) := rfl

@[simp]
theorem Zipper.begin_suff {l : List α} : (Zipper.begin l).suff = l := rfl

@[simp]
theorem Zipper.begin_pref {l : List α} : (Zipper.begin l).pref = [] := rfl

@[simp]
theorem Zipper.end_pref {l : List α} : (Zipper.end l).pref = l := by simp [Zipper.end,pref]

@[simp]
theorem Zipper.end_suff {l : List α} : (Zipper.end l).suff = [] := rfl

@[simp]
theorem Zipper.tail_suff {l : List α} {s : Zipper l} (h : s.suff = hd::tl) : (s.tail h).suff = tl := rfl

end List

theorem Specs.pure' [Monad m] [WPMonad m ps] {P : Assertion ps} {Q : PostCond α ps}
    (h : P ⊢ₛ Q.1 a) :
    ⦃P⦄ Pure.pure (f:=m) a ⦃Q⦄ := Triple.pure a h

@[spec]
theorem Specs.pure {m : Type → Type} {ps : PostShape} [Monad m] [WPMonad m ps] {α} {a : α} {Q : PostCond α ps} :
  ⦃Q.1 a⦄ Pure.pure (f:=m) a ⦃Q⦄ := Specs.pure' .rfl

theorem Specs.bind' [Monad m] [WPMonad m ps] {x : m α} {f : α → m β} {P : Assertion ps} {Q : PostCond β ps}
    (h : ⦃P⦄ x ⦃(fun a => wp⟦f a⟧ Q, Q.2)⦄) :
    ⦃P⦄ (x >>= f) ⦃Q⦄ := Triple.bind x f h (fun _ => .rfl)

@[spec]
theorem Specs.bind {m : Type → Type} {ps : PostShape} [Monad m] [WPMonad m ps] {α β} {x : m α} {f : α → m β} {Q : PostCond β ps} :
  ⦃wp⟦x⟧ (fun a => wp⟦f a⟧ Q, Q.2)⦄ (x >>= f) ⦃Q⦄ := Specs.bind' .rfl

@[spec]
theorem Specs.ite {α m ps} {P : Assertion ps} {Q : PostCond α ps} (c : Prop) [Decidable c] [WP m ps] (t : m α) (e : m α)
    (ifTrue : c → ⦃P⦄ t ⦃Q⦄) (ifFalse : ¬c → ⦃P⦄ e ⦃Q⦄) :
    ⦃P⦄ if c then t else e ⦃Q⦄ := by
  split <;> apply_rules

@[spec]
theorem Specs.dite {α m ps} {P : Assertion ps} {Q : PostCond α ps} (c : Prop) [Decidable c] [WP m ps] (t : c → m α) (e : ¬ c → m α)
    (ifTrue : (h : c) → ⦃P⦄ t h ⦃Q⦄) (ifFalse : (h : ¬ c) → ⦃P⦄ e h ⦃Q⦄) :
    ⦃P⦄ if h : c then t h else e h ⦃Q⦄ := by
  split <;> apply_rules

@[spec]
theorem Specs.forIn'_list {α : Type} {β : Type} {m : Type → Type v} {ps : PostShape}
    [Monad m] [WPMonad m ps]
    {xs : List α} {init : β} {f : (a : α) → a ∈ xs → β → m (ForInStep β)}
    (inv : PostCond (β × List.Zipper xs) ps)
    (step : ∀ b rpref x (hx : x ∈ xs) suff (h : xs = rpref.reverse ++ x :: suff),
        ⦃inv.1 (b, ⟨rpref, x::suff, by simp [h]⟩)⦄
        f x hx b
        ⦃(fun r => match r with
                   | .yield b' => inv.1 (b', ⟨x::rpref, suff, by simp [h]⟩)
                   | .done b' => inv.1 (b', ⟨xs.reverse, [], by simp⟩), inv.2)⦄) :
    ⦃inv.1 (init, ⟨[], xs, by simp⟩)⦄ forIn' xs init f ⦃(fun b => inv.1 (b, ⟨xs.reverse, [], by simp⟩), inv.2)⦄ := by
  suffices h : ∀ rpref suff (h : xs = rpref.reverse ++ suff),
      ⦃inv.1 (init, ⟨rpref, suff, by simp [h]⟩)⦄
      forIn' (m:=m) suff init (fun a ha => f a (by simp[h,ha]))
      ⦃(fun b => inv.1 (b, ⟨xs.reverse, [], by simp [h]⟩), inv.2)⦄
    from h [] xs rfl
  intro rpref suff h
  induction suff generalizing rpref init
  case nil => apply Triple.pure; simp [h]
  case cons x suff ih =>
    simp only [List.forIn'_cons]
    apply Triple.bind
    case hx => exact step init rpref x (by simp[h]) suff h
    case hf =>
      intro r
      split
      next => apply Triple.pure; simp [h]
      next b =>
        simp
        have := @ih b (x::rpref) (by simp [h])
        simp at this
        exact this

-- using the postcondition as a constant invariant:
theorem Specs.forIn'_list_const_inv {α : Type} {β : Type} {m : Type → Type v} {ps : PostShape}
  [Monad m] [WPMonad m ps]
  {xs : List α} {init : β} {f : (a : α) → a ∈ xs → β → m (ForInStep β)}
  {inv : PostCond β ps}
  (step : ∀ x (hx : x ∈ xs) b,
      ⦃inv.1 b⦄
      f x hx b
      ⦃(fun r => match r with | .yield b' => inv.1 b' | .done b' => inv.1 b', inv.2)⦄) :
  ⦃inv.1 init⦄ forIn' xs init f ⦃inv⦄ :=
    Specs.forIn'_list (fun p => inv.1 p.1, inv.2) (fun b _ x hx _ _ => step x hx b)

@[spec]
theorem Specs.forIn_list {α : Type} {β : Type} {m : Type → Type v} {ps : PostShape}
    [Monad m] [WPMonad m ps]
    {xs : List α} {init : β} {f : α → β → m (ForInStep β)}
    (inv : PostCond (β × List.Zipper xs) ps)
    (step : ∀ b rpref x suff (h : xs = rpref.reverse ++ x :: suff),
        ⦃inv.1 (b, ⟨rpref, x::suff, by simp [h]⟩)⦄
        f x b
        ⦃(fun r => match r with
                   | .yield b' => inv.1 (b', ⟨x::rpref, suff, by simp [h]⟩)
                   | .done b' => inv.1 (b', ⟨xs.reverse, [], by simp⟩), inv.2)⦄) :
    ⦃inv.1 (init, ⟨[], xs, by simp⟩)⦄ forIn xs init f ⦃(fun b => inv.1 (b, ⟨xs.reverse, [], by simp⟩), inv.2)⦄ := by
  simp only [← forIn'_eq_forIn]
  exact Specs.forIn'_list inv (fun b rpref x _ suff h => step b rpref x suff h)

-- using the postcondition as a constant invariant:
theorem Specs.forIn_list_const_inv {α : Type} {β : Type} {m : Type → Type v} {ps : PostShape}
  [Monad m] [WPMonad m ps]
  {xs : List α} {init : β} {f : α → β → m (ForInStep β)}
  {inv : PostCond β ps}
  (step : ∀ hd b,
      ⦃inv.1 b⦄
      f hd b
      ⦃(fun r => match r with | .yield b' => inv.1 b' | .done b' => inv.1 b', inv.2)⦄) :
  ⦃inv.1 init⦄ forIn xs init f ⦃inv⦄ :=
    Specs.forIn_list (fun p => inv.1 p.1, inv.2) (fun b _ hd _ _ => step hd b)

@[spec]
theorem Specs.foldlM_list {α : Type} {β : Type} {m : Type → Type v} {ps : PostShape}
  [Monad m] [WPMonad m ps]
  {xs : List α} {init : β} {f : β → α → m β}
  (inv : PostCond (β × List.Zipper xs) ps)
  (step : ∀ b rpref x suff (h : xs = rpref.reverse ++ x :: suff),
      ⦃inv.1 (b, ⟨rpref, x::suff, by simp [h]⟩)⦄
      f b x
      ⦃(fun b' => inv.1 (b', ⟨x::rpref, suff, by simp [h]⟩), inv.2)⦄) :
  ⦃inv.1 (init, ⟨[], xs, by simp⟩)⦄ List.foldlM f init xs ⦃(fun b => inv.1 (b, ⟨xs.reverse, [], by simp⟩), inv.2)⦄ := by
  have : xs.foldlM f init = forIn xs init (fun a b => .yield <$> f b a) := by
    simp only [List.forIn_yield_eq_foldlM, id_map']
  rw[this]
  apply Specs.forIn_list inv
  simp only [Triple, map_map, PredTrans.map_apply]
  exact step

-- using the postcondition as a constant invariant:
theorem Specs.foldlM_list_const_inv {α : Type} {β : Type} {m : Type → Type v} {ps : PostShape}
  [Monad m] [WPMonad m ps]
  {xs : List α} {init : β} {f : β → α → m β}
  {inv : PostCond β ps}
  (step : ∀ hd b,
      ⦃inv.1 b⦄
      f b hd
      ⦃(fun b' => inv.1 b', inv.2)⦄) :
  ⦃inv.1 init⦄ List.foldlM f init xs ⦃inv⦄ :=
    Specs.foldlM_list (fun p => inv.1 p.1, inv.2) (fun b _ hd _ _ => step hd b)

@[spec]
theorem Specs.forIn'_range {β : Type} {m : Type → Type v} {ps : PostShape}
    [Monad m] [WPMonad m ps]
    {xs : Std.Range} {init : β} {f : (a : Nat) → a ∈ xs → β → m (ForInStep β)}
    (inv : PostCond (β × List.Zipper xs.toList) ps)
    (step : ∀ b rpref x (hx : x ∈ xs) suff (h : xs.toList = rpref.reverse ++ x :: suff),
        ⦃inv.1 (b, ⟨rpref, x::suff, by simp [h]⟩)⦄
        f x hx b
        ⦃(fun r => match r with
                   | .yield b' => inv.1 (b', ⟨x::rpref, suff, by simp [h]⟩)
                   | .done b' => inv.1 (b', ⟨xs.toList.reverse, [], by simp⟩), inv.2)⦄) :
    ⦃inv.1 (init, ⟨[], xs.toList, by simp⟩)⦄ forIn' xs init f ⦃(fun b => inv.1 (b, ⟨xs.toList.reverse, [], by simp⟩), inv.2)⦄ := by
  simp only [Std.Range.forIn'_eq_forIn'_range', Std.Range.size, Std.Range.size.eq_1]
  apply Specs.forIn'_list inv (fun b rpref x hx suff h => step b rpref x (Std.Range.mem_of_mem_range' hx) suff h)

@[spec]
theorem Specs.forIn_range {β : Type} {m : Type → Type v} {ps : PostShape}
    [Monad m] [WPMonad m ps]
    {xs : Std.Range} {init : β} {f : Nat → β → m (ForInStep β)}
    (inv : PostCond (β × List.Zipper xs.toList) ps)
    (step : ∀ b rpref x suff (h : xs.toList = rpref.reverse ++ x :: suff),
        ⦃inv.1 (b, ⟨rpref, x::suff, by simp [h]⟩)⦄
        f x b
        ⦃(fun r => match r with
                   | .yield b' => inv.1 (b', ⟨x::rpref, suff, by simp [h]⟩)
                   | .done b' => inv.1 (b', ⟨xs.toList.reverse, [], by simp⟩), inv.2)⦄) :
    ⦃inv.1 (init, ⟨[], xs.toList, by simp⟩)⦄ forIn xs init f ⦃(fun b => inv.1 (b, ⟨xs.toList.reverse, [], by simp⟩), inv.2)⦄ := by
  simp only [Std.Range.forIn_eq_forIn_range', Std.Range.size]
  apply Specs.forIn_list inv step

@[spec]
theorem Specs.forIn'_array {α : Type} {β : Type} {m : Type → Type v} {ps : PostShape}
    [Monad m] [WPMonad m ps]
    {xs : Array α} {init : β} {f : (a : α) → a ∈ xs → β → m (ForInStep β)}
    (inv : PostCond (β × List.Zipper xs.toList) ps)
    (step : ∀ b rpref x (hx : x ∈ xs) suff (h : xs.toList = rpref.reverse ++ x :: suff),
        ⦃inv.1 (b, ⟨rpref, x::suff, by simp [h]⟩)⦄
        f x hx b
        ⦃(fun r => match r with
                   | .yield b' => inv.1 (b', ⟨x::rpref, suff, by simp [h]⟩)
                   | .done b' => inv.1 (b', ⟨xs.toList.reverse, [], by simp⟩), inv.2)⦄) :
    ⦃inv.1 (init, ⟨[], xs.toList, by simp⟩)⦄ forIn' xs init f ⦃(fun b => inv.1 (b, ⟨xs.toList.reverse, [], by simp⟩), inv.2)⦄ := by
  cases xs
  simp
  apply Specs.forIn'_list inv (fun b rpref x hx suff h => step b rpref x (by simp[hx]) suff h)

@[spec]
theorem Specs.forIn_array {α : Type} {β : Type} {m : Type → Type v} {ps : PostShape}
    [Monad m] [WPMonad m ps]
    {xs : Array α} {init : β} {f : α → β → m (ForInStep β)}
    (inv : PostCond (β × List.Zipper xs.toList) ps)
    (step : ∀ b rpref x suff (h : xs.toList = rpref.reverse ++ x :: suff),
        ⦃inv.1 (b, ⟨rpref, x::suff, by simp [h]⟩)⦄
        f x b
        ⦃(fun r => match r with
                   | .yield b' => inv.1 (b', ⟨x::rpref, suff, by simp [h]⟩)
                   | .done b' => inv.1 (b', ⟨xs.toList.reverse, [], by simp⟩), inv.2)⦄) :
    ⦃inv.1 (init, ⟨[], xs.toList, by simp⟩)⦄ forIn xs init f ⦃(fun b => inv.1 (b, ⟨xs.toList.reverse, [], by simp⟩), inv.2)⦄ := by
  cases xs
  simp
  apply Specs.forIn_list inv step

@[spec]
theorem Specs.foldlM_array {α : Type} {β : Type} {m : Type → Type v} {ps : PostShape}
  [Monad m] [WPMonad m ps]
  {xs : Array α} {init : β} {f : β → α → m β}
  (inv : PostCond (β × List.Zipper xs.toList) ps)
  (step : ∀ b rpref x suff (h : xs.toList = rpref.reverse ++ x :: suff),
      ⦃inv.1 (b, ⟨rpref, x::suff, by simp [h]⟩)⦄
      f b x
      ⦃(fun b' => inv.1 (b', ⟨x::rpref, suff, by simp [h]⟩), inv.2)⦄) :
  ⦃inv.1 (init, ⟨[], xs.toList, by simp⟩)⦄ Array.foldlM f init xs ⦃(fun b => inv.1 (b, ⟨xs.toList.reverse, [], by simp⟩), inv.2)⦄ := by
  cases xs
  simp
  apply Specs.foldlM_list inv step

end MPL
