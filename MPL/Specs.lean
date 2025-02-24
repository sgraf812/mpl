import MPL.Triple
import MPL.SpecAttr

namespace MPL

--@[spec]
theorem Specs.forIn_list {α β} {m : Type → Type}
  [Monad m] [LawfulMonad m] [WP m ps] [WPMonad m ps]
  {xs : List α} {init : β} {f : α → β → m (ForInStep β)}
  (inv : PostCond (List α × β) ps)
  (hstep : ∀ hd tl b,
      ⦃inv.1 (hd :: tl, b)⦄
      wp⟦f hd b⟧
      ⦃(fun r => match r with | .yield b' => inv.1 (tl, b') | .done b' => inv.1 ([], b'), inv.2)⦄) :
  ⦃inv.1 (xs, init)⦄ wp⟦forIn xs init f⟧ ⦃(fun b' => inv.1 ([], b'), inv.2)⦄ := by
    induction xs generalizing init
    case nil => apply triple_pure; simp
    case cons hd tl ih =>
      simp only [List.forIn_cons]
      apply triple_bind
      case hx => exact hstep hd tl init
      case hf =>
        intro b
        split
        · apply triple_pure; simp
        · exact ih

--@[spec]
theorem Specs.foldlM_list {α β} {m : Type → Type}
  [Monad m] [LawfulMonad m] [WP m ps] [WPMonad m ps]
  {xs : List α} {init : β} {f : β → α → m β}
  (inv : PostCond (List α × β) ps)
  (hstep : ∀ hd tl b,
      ⦃inv.1 (hd :: tl, b)⦄
      wp⟦f b hd⟧
      ⦃(fun b' => inv.1 (tl, b'), inv.2)⦄) :
  ⦃inv.1 (xs, init)⦄ wp⟦List.foldlM f init xs⟧ ⦃(fun b' => inv.1 ([], b'), inv.2)⦄ := by
  have : xs.foldlM f init = forIn xs init (fun a b => .yield <$> f b a) := by
    simp only [List.forIn_yield_eq_foldlM, id_map']
  rw[this]
  apply Specs.forIn_list inv
  simp only [triple, wp_map, PredTrans.map_apply]
  exact hstep

end MPL
