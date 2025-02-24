@[ext]
structure Idd (α : Type u) where
  run : α

def Idd.pure (a : α) : Idd α := ⟨a⟩
def Idd.bind (x : Idd α) (f : α → Idd β) : Idd β := f x.run
instance : Monad Idd where
  pure := Idd.pure
  bind := Idd.bind

instance : LawfulMonad Idd where
  bind_pure_comp := by intros; constructor
  pure_bind := by intros; constructor
  bind_assoc := by intros; constructor
  bind_map := by intros; constructor
  map_const := sorry
  id_map := sorry
  pure_seq := sorry
  seqLeft_eq := sorry
  seqRight_eq := sorry
