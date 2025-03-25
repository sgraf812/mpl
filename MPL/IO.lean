import MPL.WPMonad

open MPL

structure Universe where
  U : Type
  El : U → Type

def Elts (u : Universe) : Type := Σ x, u.El x

abbrev Addr := Fin
def Heap (u : Universe) n := Addr n → Elts u

axiom IO.wp {α ε} (x : EIO ε α) : PredTrans (.except ε .pure) α
axiom IO.wp_pure {α ε} (a : α) :
  IO.wp (pure (f := EIO ε) a) = PredTrans.pure a
axiom IO.wp_bind {α β ε} (x : EIO ε α) (f : α → EIO ε β) :
  IO.wp (x >>= f) = IO.wp x >>= fun a => IO.wp (f a)

noncomputable instance IO.instWP : WP (EIO ε) (.except ε .pure) where
  wp := IO.wp

axiom IO.instLawfulMonad {ε} : LawfulMonad (EIO ε)
local instance : LawfulMonad (EIO ε) := IO.instLawfulMonad

noncomputable instance IO.instWPMonad : WPMonad (EIO ε) (.except ε .pure) where
  pure_pure := IO.wp_pure
  bind_bind := IO.wp_bind
