-- This type exists purely because of the following annoying simp rules:
#check Id.map_eq
#check Id.bind_eq
#check Id.pure_eq

@[irreducible]
def Idd (α : Type u) := α

def Idd.run (x : Idd α) : α := cast (by unfold Idd; rfl) x
def Idd.pure (a : α) : Idd α := cast (by unfold Idd; rfl) a

@[simp]
theorem Idd.run_pure (a : α) : Idd.run (Idd.pure a) = a := by with_unfolding_all rfl

def Idd.bind (x : Idd α) (f : α → Idd β) : Idd β := f x.run
instance : Monad Idd where
  pure := Idd.pure
  bind := Idd.bind

instance : LawfulMonad Idd where
  bind_pure_comp := by intros; constructor
  pure_bind := by intros; with_unfolding_all constructor
  bind_assoc := by intros; constructor
  bind_map := by intros; constructor
  map_const := sorry
  id_map := sorry
  pure_seq := sorry
  seqLeft_eq := sorry
  seqRight_eq := sorry
