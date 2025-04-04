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

class GetTy (σ : Type) (σs : List Type) where
  get : SVal σs σ

instance : GetTy σ (σ :: σs) where
  get := fun s => pure s

instance [GetTy σ₁ σs] : GetTy σ₁ (σ₂ :: σs) where
  get := fun _ => GetTy.get

def getThe {σs : List Type} (σ : Type) [GetTy σ σs] : SVal σs σ := GetTy.get
@[simp] theorem getThe_here {σs : List Type} (σ : Type) (s : σ) : getThe (σs := σ::σs) σ s = pure s := rfl
@[simp] theorem getThe_there {σs : List Type} [GetTy σ σs] (σ' : Type) (s : σ') : getThe (σs := σ'::σs) σ s = getThe (σs := σs) σ := rfl

def EscapeFun (σs : List Type) := { f : ∀ α, SVal σs α → α // ∀ α (a : α), f α (pure a) = a }
def EscapeFun.id : EscapeFun [] := ⟨fun _ m => m, fun _ _ => rfl⟩
def EscapeFun.cons (s : σ) (fn : EscapeFun σs) : EscapeFun (σ::σs) :=
  ⟨fun α m => fn.1 α (m s), fn.2⟩

def GetTy.applyEscape {σs : List Type} (f : SVal σs σ) (escape : EscapeFun σs) : σ := escape.1 σ f
@[simp]
theorem GetTy.applyEscape_pure {σs : List Type} {s : σ} {escape : EscapeFun σs} :
  GetTy.applyEscape (σs:=σs) (pure s) escape = s := by simp[applyEscape, escape.property]

@[simp]
theorem GetTy.applyEscape_id {m : SVal [] α} :
  GetTy.applyEscape m EscapeFun.id = m := rfl

@[simp]
theorem GetTy.applyEscape_cons {σs : List Type} {s : σ} {m : SVal (σ::σs) α} {escape : EscapeFun σs} :
  GetTy.applyEscape (σs:=(σ::σs)) m (SVal.EscapeFun.cons s escape) = SVal.GetTy.applyEscape (m s) escape := rfl
