import Lean

namespace MPL.Util

open Lean Meta Tactic

inductive Uses where
  | zero
  | one
  | many
deriving BEq, Ord, Inhabited

def Uses.add : Uses → Uses → Uses
  | .zero, b => b
  | a, .zero => a
  | _, _ => .many

def Uses.toNat : Uses → Nat
  | .zero => 0
  | .one => 1
  | .many => 2

def Uses.fromNat : Nat → Uses
  | 0 => .zero
  | 1 => .one
  | _ => .many

instance : Add Uses where
  add := Uses.add

abbrev FVarUses := Std.HashMap FVarId Uses

def FVarUses.add (a b : FVarUses) : FVarUses :=
  a.fold (init := b) fun acc k v => acc.alter k fun
    | none => some v
    | some v' => some (v + v')

instance : Add FVarUses where
  add := FVarUses.add

inductive BVarUses (n : Nat) where
  | none
  | some (uses : Vector Uses n) -- indexed by BVars in reverse order

def BVarUses.single {numBVars : Nat} (n : Nat) (_ : n < numBVars := by get_elem_tactic) : BVarUses numBVars :=
  -- NB: BVarUses is indexed by BVars in reverse order
  .some <| .ofFn fun (i : Fin numBVars) => if i.val = numBVars - 1 - n then .one else .zero

def BVarUses.pop {numBVars : Nat} : BVarUses (numBVars + 1) → (Uses × BVarUses numBVars)
  | .none => (.zero, .none)
  | .some uses => (uses.back, .some uses.pop)

def BVarUses.add {numBVars : Nat} (a b : BVarUses numBVars) : BVarUses numBVars := match a, b with
  | .none, b => b
  | a, .none => a
  | .some a, .some b => .some (a.zipWith (fun a b => a + b) b)

instance : Add (BVarUses numBVars) where
  add := BVarUses.add

def over1Of2 (f : α → α) (x : α × β) : α × β := (f x.1, x.2)

def addMData (d : MData) (e : Expr) : Expr := match e with
  | .mdata d' e => .mdata (d.mergeBy (fun _ new _ => new) d') e
  | _ => .mdata d e

def countUses (e : Expr) (subst : Array FVarId := #[]) : MetaM (Expr × FVarUses) := match e with
  | .bvar n =>
    if _ : n < subst.size then
      return (e, {(subst[n], .one)})
    else
      throwError "BVar index out of bounds: {n} >= {subst.size}"
  | .fvar fvarId => return (e, {(fvarId, .one)})
  | .letE x ty val body b => do
    let fv ← mkFreshFVarId
    let (ty, fvs₁) ← countUses ty subst
    let (val, fvs₂) ← countUses val subst
    let (body, fvs₃) ← countUses body (subst.push fv)
    let fvs := (fvs₁ + fvs₂ + fvs₃)
    let uses := fvs.getD fv .zero
    let fvs := fvs.erase fv
    let body := addMData (MData.empty.setNat `uses uses.toNat) body
    return (.letE x ty val body b, fvs)
  | .lam x ty body bi => do
    let fv ← mkFreshFVarId
    let (ty, fvs₁) ← countUses ty subst
    let (body, fvs₂) ← countUses body (subst.push fv)
    let fvs := (fvs₁ + fvs₂).erase fv
    return (.lam x ty body bi, fvs) -- NB: We do not track uses of lam-bound x
  | .forallE x ty body bi => do -- (almost) identical to lam
    let fv ← mkFreshFVarId
    let (ty, fvs₁) ← countUses ty subst
    let (body, fvs₂) ← countUses body (subst.push fv)
    let fvs := (fvs₁ + fvs₂).erase fv
    return (.forallE x ty body bi, fvs) -- NB: We do not track uses of forall-bound x
  | .proj s i e => over1Of2 (Expr.proj s i) <$> countUses e subst
  | .mdata d e => over1Of2 (Expr.mdata d) <$> countUses e subst
  | .app f a => do
    let (f, fvarUses₁) ← countUses f subst
    let (a, fvarUses₂) ← countUses a subst
    return (.app f a, fvarUses₁ + fvarUses₂)
  | .lit .. | .const .. | .sort .. | .mvar .. => return (e, {})

def elimLetsCore (e : Expr) : MetaM Expr := StateRefT'.run' (s := Std.HashSet.empty) do
  -- Figure out if we can make this work with Core.transform.
  -- I think that would entail keeping track of BVar shifts in `pre` and `post`.
  let pre (e : Expr) : StateRefT (Std.HashSet FVarId) MetaM TransformStep := do
    match e with
    | .letE _ _ val body _ => do
      let .mdata d e := body | return .continue
      let uses := Uses.fromNat (d.getNat `uses 2) -- 2 goes to .many
      if uses == .many then return .continue
      return .visit (body.instantiate1 val) -- urgh O(n^2). See comment above
    | _ => return .continue
  Meta.transform e (pre := pre)

def elimLets (mvar : MVarId) : MetaM MVarId := do
  let (ty, fvarUses) ← countUses (← mvar.getType)
  let mut fvs := #[]
  let mut vals := #[]
  for (fvarId, uses) in fvarUses do
    if uses == .many then continue
    let .some val ← fvarId.getValue? | continue
    fvs := fvs.push (mkFVar fvarId)
    vals := vals.push val
  let ty := ty.replaceFVars fvs vals
  let ty ← elimLetsCore ty
  let newMVar ← mkFreshExprSyntheticOpaqueMVar ty (← mvar.getTag)
  mvar.assign newMVar
  let mut mvar := newMVar.mvarId!
  for fvarId in fvs do
    mvar ← mvar.tryClear fvarId.fvarId!
  return mvar
