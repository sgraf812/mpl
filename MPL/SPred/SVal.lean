import Lean
import Init.Data.List

namespace MPL

/-- A value indexed by a list of states. -/
abbrev SVal (σs : List Type) (α : Type) := match σs with
| [] => α
| σ :: σs => σ → SVal σs α
/- Note about the reducibility of SVal:
We need SVal to be reducible, so that simp can apply lemmas such as
  lemma ite_app {c:Prop} [Decidable c] (t e : α → β) (a : α) : (if c then t else e) a = if c then t a else e a
-/

namespace SVal

def pure {σs : List Type} (a : α) : SVal σs α := match σs with
| [] => a
| σ :: _ => fun (_ : σ) => pure a
@[simp] theorem pure_nil (a : α) : pure (σs:=[]) a = a := rfl
@[simp] theorem pure_cons {s : σ} (a : α) : pure (σs:=σ::σs) a s = pure a := rfl

/-- Pack all state variables into a tuple.
This type will be looked up `by assumption` to implement idiom notation. -/
def StateTuple (σs : List Type) := match σs with
| [] => Unit
| σ :: σs => σ × StateTuple σs

/-- Run an `SVal` on a tuple of state variables.
Used like `uncurry f (by assumption)` to implement idiom notation. -/
def uncurry {σs : List Type} (f : SVal σs σ) (tuple : StateTuple σs) : σ := match σs with
| [] => f
| _ :: _ => uncurry (f tuple.1) tuple.2

@[simp]
theorem uncurry_pure {σs : List Type} {s : σ} {tuple : StateTuple σs} :
  uncurry (σs:=σs) (pure s) tuple = s := by induction σs <;> simp[uncurry, *]

@[simp]
theorem uncurry_nil {m : SVal [] α} :
  uncurry m () = m := rfl

@[simp]
theorem uncurry_cons {σs : List Type} {s : σ} {m : SVal (σ::σs) α} {tuple : StateTuple σs} :
  uncurry (σs:=(σ::σs)) m (s, tuple) = uncurry (m s) tuple := rfl

/-- Function used to implement idiom notation.
```
example : SVal [Nat, Bool] := idiom fun tpl => SVal.pure (1 + uncurry (getThe Nat) + 3)
```
 -/
def idiom {σs : List Type} (f : StateTuple σs → SVal σs α) : SVal σs α := match σs with
| [] => f ()
| _ :: _ => fun s => idiom (fun tuple => f (s, tuple) s)
@[simp] theorem idiom_nil {f : StateTuple [] → SVal [] α} : idiom f = f () := rfl
@[simp] theorem idiom_cons {σs : List Type} {f : StateTuple (σ::σs) → SVal (σ::σs) α} {s : σ} : idiom f s = idiom (fun tuple => f (s, tuple) s) := rfl
@[simp] theorem idiom_pure {σs : List Type} {f : SVal σs α} : idiom (fun _ => f) = f := by induction σs <;> simp[idiom, *]

class GetTy (σ : Type) (σs : List Type) where
  get : SVal σs σ

instance : GetTy σ (σ :: σs) where
  get := fun s => pure s

instance [GetTy σ₁ σs] : GetTy σ₁ (σ₂ :: σs) where
  get := fun _ => GetTy.get

def getThe {σs : List Type} (σ : Type) [GetTy σ σs] : SVal σs σ := GetTy.get
@[simp] theorem getThe_here {σs : List Type} (σ : Type) (s : σ) : getThe (σs := σ::σs) σ s = pure s := rfl
@[simp] theorem getThe_there {σs : List Type} [GetTy σ σs] (σ' : Type) (s : σ') : getThe (σs := σ'::σs) σ s = getThe (σs := σs) σ := rfl
