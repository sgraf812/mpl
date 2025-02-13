import Init
import Mathlib.Data.Set.Basic

structure Region where

structure Eff (rs : Set Region) (α : Type) where
  unsafeGet : BaseIO α

def Eff.pure (x : α) : Eff rs α :=
  Eff.mk (Pure.pure x)
def Eff.bind (x : Eff rs α) (f : α → Eff rs β) : Eff rs β :=
  Eff.mk (x.unsafeGet >>= fun a => (f a).unsafeGet)
instance : Monad (Eff rs) where
  pure := Eff.pure
  bind := Eff.bind

unsafe def Eff.runPure (e : ∀{rs}, Eff rs α) : α :=
  unsafeBaseIO (e.unsafeGet (rs := ∅))

def Eff.weaken {_ : rs₁ ⊆ rs₂} (e : Eff rs₁ a) : Eff rs₂ a :=
  Eff.mk e.unsafeGet

-- | A handle to a strict mutable state of type @s@
class State (σ : Type) (r : Region) where
  unsafeGet : IO.Ref σ

def State.run (s : σ) (c : ∀{r}, [State σ r] → Eff ({r} ∪ rs) α) : Eff rs (α × σ) := do
  Eff.mk (IO.mkRef s)
