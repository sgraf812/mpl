import MPL.Triple
import MPL.SpecAttr

namespace MPL

namespace List

theorem tail_of_cons_suffix : hd::tl <:+ l → tl <:+ l := by
  intro ⟨pre, h⟩
  use (pre ++ [hd])
  simp[h]

-- TODO: Replace l by α, remove property, define toList instead?
@[ext]
structure Zipper (l : List α) where
  rpref : List α
  suff : List α
  property : rpref.reverse ++ suff = l

@[simp]
abbrev Zipper.pref {α} {l : List α} (s : List.Zipper l) : List α := s.rpref.reverse

def Zipper.suffix (s : List.Zipper l) : s.suff <:+ l := ⟨s.pref, s.property⟩
def Zipper.prefix (s : List.Zipper l) : s.pref <+: l := ⟨s.suff, s.property⟩
def Zipper.begin {l : List α} : Zipper l := ⟨[],l,rfl⟩
def Zipper.end {l : List α} : Zipper l := ⟨l.reverse,[],by simp⟩
def Zipper.atSuff {l suff : List α} (h : suff <:+ l): Zipper l := ⟨l.reverse.drop suff.length,suff,sorry⟩
def Zipper.tail (s : Zipper l) (h : s.suff = hd::tl) : Zipper l :=
  { rpref := hd::s.rpref, suff := tl, property := by simp[s.property, ←h] }
--theorem Zipper.tail_is_tail (s : Zipper l) (h : s.suff = hd::tl) : (s.tail h).suff = tl := by simp[tail]
@[simp]
theorem Zipper.begin_eq_end_iff_nil : @Zipper.begin _ l = @Zipper.end _ l ↔ l = [] := by
  constructor <;> simp[begin, Zipper.end]

@[simp]
theorem Zipper.nil_begin_eq_end : @Zipper.begin α [] = @Zipper.end α [] := rfl

@[simp]
theorem Zipper.begin_suff {l : List α} : (@Zipper.begin α l).suff = l := rfl

@[simp]
theorem Zipper.begin_pref {l : List α} : (@Zipper.begin α l).pref = [] := rfl

@[simp]
theorem Zipper.end_pref {l : List α} : (@Zipper.end α l).pref = l := by simp[Zipper.end,pref]

@[simp]
theorem Zipper.end_suff {l : List α} : (@Zipper.end α l).suff = [] := rfl

@[simp]
theorem Zipper.tail_suff {l : List α} {s : Zipper l} (h : s.suff = hd::tl) : (s.tail h).suff = tl := rfl

@[simp]
theorem Zipper.atSuff_nil_end (l : List α) : @Zipper.atSuff _ l [] List.nil_suffix = Zipper.end := rfl

@[simp]
theorem Zipper.atSuff_rfl_begin (l : List α) : @Zipper.atSuff _ l l List.suffix_rfl = Zipper.begin := by
  simp[begin, atSuff]

@[simp]
theorem Zipper.atSuff_tail (l : List α) (h : hd::tl <:+ l): (Zipper.atSuff h).tail rfl = Zipper.atSuff (tail_of_cons_suffix h) := by
  induction l
  case nil => simp at h
  case cons hd' tl' ih => sorry -- later

end List

#check Subtype
--@[spec]
theorem Specs.forIn_list {α β} ⦃m : Type → Type⦄
  [Monad m] [LawfulMonad m] [WP m ps] [WPMonad m ps]
  {xs : List α} {init : β} {f : α → β → m (ForInStep β)}
  (inv : PostCond (β × List.Zipper xs) ps)
  (step : ∀ b rpref x suff (h : xs = rpref.reverse ++ x :: suff),
      ⦃inv.1 (b, ⟨rpref, x::suff, by simp[h]⟩)⦄
      f x b
      ⦃(fun r => match r with
                 | .yield b' => inv.1 (b', ⟨x::rpref, suff, by simp[h]⟩)
                 | .done b' => inv.1 (b', ⟨xs.reverse, [], by simp⟩), inv.2)⦄) :
  ⦃inv.1 (init, ⟨[], xs, by simp⟩)⦄ forIn xs init f ⦃(fun b => inv.1 (b, ⟨xs.reverse, [], by simp⟩), inv.2)⦄ := by
    suffices h : ∀ rpref suff (h : xs = rpref.reverse ++ suff), ⦃inv.1 (init, ⟨rpref, suff, by simp[h]⟩)⦄ forIn suff init f ⦃(fun b => inv.1 (b, ⟨xs.reverse, [], by simp[h]⟩), inv.2)⦄
      from h [] xs rfl
    intro rpref suff h
    induction suff generalizing rpref init
    case nil => apply triple_pure; simp[h]
    case cons x suff ih =>
      simp only [List.forIn_cons]
      apply triple_bind
      case hx => exact step init rpref x suff h
      case hf =>
        intro r
        split
        next => apply triple_pure; simp[h]
        next b =>
          simp
          have := @ih b (x::rpref) (by simp[h])
          simp at this
          exact this

-- using the postcondition as a constant invariant:
@[spec]
theorem Specs.forIn_list_const_inv {α β : Type} ⦃m : Type → Type⦄
  [Monad m] [LawfulMonad m] [WP m ps] [WPMonad m ps]
  {xs : List α} {init : β} {f : α → β → m (ForInStep β)}
  {inv : PostCond β ps}
  (step : ∀ hd b,
      ⦃inv.1 b⦄
      f hd b
      ⦃(fun r => match r with | .yield b' => inv.1 b' | .done b' => inv.1 b', inv.2)⦄) :
  ⦃inv.1 init⦄ forIn xs init f ⦃inv⦄ :=
    Specs.forIn_list (fun p => inv.1 p.1, inv.2) (fun b _ hd _ _ => step hd b)

--@[spec]
theorem Specs.foldlM_list {α β} ⦃m : Type → Type⦄
  [Monad m] [LawfulMonad m] [WP m ps] [WPMonad m ps]
  {xs : List α} {init : β} {f : β → α → m β}
  (inv : PostCond (β × List.Zipper xs) ps)
  (step : ∀ b rpref x suff (h : xs = rpref.reverse ++ x :: suff),
      ⦃inv.1 (b, ⟨rpref, x::suff, by simp[h]⟩)⦄
      f b x
      ⦃(fun b' => inv.1 (b', ⟨x::rpref, suff, by simp[h]⟩), inv.2)⦄) :
  ⦃inv.1 (init, ⟨[], xs, by simp⟩)⦄ List.foldlM f init xs ⦃(fun b => inv.1 (b, ⟨xs.reverse, [], by simp⟩), inv.2)⦄ := by
  have : xs.foldlM f init = forIn xs init (fun a b => .yield <$> f b a) := by
    simp only [List.forIn_yield_eq_foldlM, id_map']
  rw[this]
  apply Specs.forIn_list inv
  simp only [triple, wp_map, PredTrans.map_apply]
  exact step

-- using the postcondition as a constant invariant:
@[spec]
theorem Specs.foldlM_list_const_inv {α β : Type} ⦃m : Type → Type⦄
  [Monad m] [LawfulMonad m] [WP m ps] [WPMonad m ps]
  {xs : List α} {init : β} {f : β → α → m β}
  {inv : PostCond β ps}
  (step : ∀ hd b,
      ⦃inv.1 b⦄
      f b hd
      ⦃(fun b' => inv.1 b', inv.2)⦄) :
  ⦃inv.1 init⦄ List.foldlM f init xs ⦃inv⦄ :=
    Specs.foldlM_list (fun p => inv.1 p.1, inv.2) (fun b _ hd _ _ => step hd b)

end MPL
