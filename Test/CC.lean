import MPL
import Std.Data.HashMap
import Std.Data.HashMap.Lemmas

namespace Acc

instance wfRel {r : α → α → Prop} : WellFoundedRelation { val // Acc r val } where
  rel := InvImage r (·.1)
  wf  := ⟨fun ac => InvImage.accessible _ ac.2⟩

end Acc

namespace WellFounded

/-- Attaches to `x` the proof that `x` is accessible in the given well-founded relation.
This can be used in recursive function definitions to explicitly use a different relation
than the one inferred by default:

```
def otherWF : WellFounded Nat := …
def foo (n : Nat) := …
termination_by otherWF.wrap n
```
-/
def wrap {α : Sort u} {r : α → α → Prop} (h : WellFounded r) (x : α) : {x : α // Acc r x} :=
  ⟨_, h.apply x⟩

end WellFounded

inductive Term where
  | var : String → Term
  | app : String → List Term → Term
  deriving Repr, BEq, Inhabited

open Term

def Term.hash : Term → UInt64
  | var x => x.hash
  | app f args => Hashable.hash (f, args.map Term.hash)

instance : Hashable Term where
  hash t := t.hash

instance : LawfulBEq Term := sorry

instance : LawfulHashable Term where
  hash_eq a b h := sorry

structure UFState.Raw where
  parent : Std.HashMap Term Term := {}

def AncestorRel (parent : Std.HashMap Term Term) : Term → Term → Prop :=
  Relation.TransGen fun par child => parent[child]? = some par

theorem ParentRel_insert (parent : Std.HashMap Term Term) (t1 t2 : Term) :
    AncestorRel parent t1 t2 → AncestorRel (parent.insert t2 t1) t1 t2 := by
  intro _
  refine .single (by simp)

theorem ParentRel_insert_Subrelation (parent : Std.HashMap Term Term) (t1 t2 : Term) (hpar : AncestorRel parent t1 t2):
    Subrelation (AncestorRel (parent.insert t2 t1)) (AncestorRel parent) := by
  intro a b h
  simp_all[AncestorRel, Std.HashMap.getElem?_insert]
  induction h
  case single t h =>
    split at h
    · simp_all
    · refine .single h
  case tail hpar hpar' ih =>
    split at hpar' <;> simp_all
    refine .tail ih ?_
    subst_vars
def Acyclic (parent : Std.HashMap Term Term) : Prop :=
  WellFounded (AncestorRel parent)

theorem ParentWF_insert (parent : Std.HashMap Term Term) (t1 t2 : Term) (hrel : AncestorRel parent t1 t2) :
    Acyclic parent → Acyclic (parent.insert t2 t1) := by
  simp[Acyclic]
  intro hwf
  constructor
  intro a
  apply Subrelation.accessible (ParentRel_insert_Subrelation parent t1 t2 hrel)
  exact hwf.apply a

def height (s : UFState.Raw) (h : Acyclic s.parent) (t : Term) : Nat :=
  match hpar : s.parent[t]? with
  | none => 0
  | some p => 1 + height s h p
termination_by h.wrap t

def UFState.Raw.find (uf : UFState.Raw) (h : Acyclic uf.parent) (t : Term) : Term × UFState.Raw :=
  match hpar : uf.parent[t]? with
  | none => (t, uf)
  | some p =>
    let (r, uf') := find uf h p
    (r, { uf' with parent := uf'.parent.insert t r })
termination_by h.wrap t

structure UFState extends UFState.Raw where
  parent_wf : Acyclic parent

#check UFState.Raw.find.induct
theorem find_root (s : UFState.Raw) (h : Acyclic s.parent) (t : Term) :
    (UFState.Raw.find s h t).1 ∉ s.parent := by
  induction t using UFState.Raw.find.induct s h
  case case1 t hpar =>
    rw[UFState.Raw.find, hpar]
    simpa only [getElem?_eq_none_iff] using hpar
  case case2 t par hpar root s' hrec ih =>
    rw[UFState.Raw.find, hpar]
    exact ih

theorem find_isRoot (s : UFState.Raw) (h : Acyclic s.parent) (t : Term) :
    t ∉ s.parent → UFState.Raw.find s h t = (t, s) := by
  induction t using UFState.Raw.find.induct s h
  case case1 t hpar =>
    rw[UFState.Raw.find, hpar]
    simp only [implies_true]
  case case2 t par hpar root s' hrec ih =>
    intro hnpar
    exfalso
    apply hnpar
    apply Std.HashMap.mem_iff_contains.2
    rw[Std.HashMap.contains_eq_isSome_getElem?]
    simp only [hpar, Option.isSome_some]

theorem find_isNotRoot (s : UFState.Raw) (h : Acyclic s.parent) (t : Term) :
    t ∈ s.parent → Relation.TransGen (AncestorRel s.parent) (UFState.Raw.find s h t).1 t := by
  induction t using UFState.Raw.find.induct s h
  case case1 t hpar =>
    rw[UFState.Raw.find, hpar]
    simp at hpar
    intro h
    contradiction
  case case2 t par hpar root s' hrec ih =>
    intro _
    rw[UFState.Raw.find, hpar]
    simp +unfoldPartialApp only [h, hrec]
    change AncestorRel s.parent par t at hpar
    simp [hrec] at ih
    by_cases hpar₂ : par ∈ s.parent
    case pos => exact .trans (ih hpar₂) (.single hpar)
    case neg =>
      have hroot := find_isRoot s h par hpar₂
      simp_all only [Prod.mk.injEq]
      exact .single hpar

theorem blah (s s' : UFState.Raw) (h : Acyclic s.parent) (t r : Term) (h2 : s.find h t = (r, s')) :
    InvImage (AncestorRel s.parent) (fun n => if t == n then r else n) = AncestorRel (s.parent.insert t r) := by
  ext x y
  simp[InvImage, AncestorRel]
  have h5 := find_root s h t
  constructor
  · intro h3
    rw[Std.HashMap.getElem?_insert]
    split
    · simp_all
      rw[Std.HashMap.getElem?_insert]
    · simp_all
      exfalso
      apply h5
      sorry -- What is the proper lemma here?


  simp[h2] at h
  simp[h2] at h
  simp[h2] at h
  simp[h2] at h
  simp[h2] at h

theorem find_wf (s : UFState.Raw) (h : Acyclic s.parent) (t : Term) :
  Acyclic (UFState.Raw.find s h t).2.parent := by
    induction t using UFState.Raw.find.induct s h
    case case1 t hpar => rw[UFState.Raw.find, hpar]; simp only [h]
    case case2 t par hpar root s' hrec ih =>
      rw[UFState.Raw.find, hpar]
      simp +unfoldPartialApp only [h, hrec]
      simp[hrec] at ih
      change AncestorRel s.parent par t at hpar
      apply InvImage.wf ?f ih
      constructor
      intro a
      constructor
      intro b
      by_cases hn : t = a
      case neg => simp[AncestorRel, hn, Std.HashMap.getElem?_insert]
      case pos =>
        simp[hn]
        constructor
        intro y hy
        simp[AncestorRel] at hy
        subst hy
        have : root ∈ s'.parent := by simp[AncestorRel] at hy; simp[hy]
      refine ParentWF_insert s'.parent root par ?hpar ih
      constructor
      intro a
      if h : t = a
      then
        simp_all[h, Std.HashMap.getElem?_insert_self]
        constructor
        intro y hy
        simp_all
      else sorry

def find (t : Term) : StateM UFState Term := do
  let s ← get
  let p := UFState.Raw.find s.toRaw s.parent_wf t
  have h : Acyclic p.2.parent := by
    unfold p
    induction t using UFState.Raw.find.induct s.toRaw s.parent_wf
    case case1 t h => rw[UFState.Raw.find, h]; simp only [s.parent_wf]
    case case2 t p' hpar r s' h ih =>
      rw[UFState.Raw.find, hpar]
      simp +unfoldPartialApp only [h, s.parent_wf, Acyclic, AncestorRel]
      simp_all only
      constructor
      intro a
      if h : t = a
      then
        simp_all[h, Std.HashMap.getElem?_insert_self]
        constructor
        intro y hy
        simp_all
    unfold UFState.Raw.find
    split
    simp[s.parent_wf]
    let h' := s'.parent_wf
    sorry
  let (r, s') := p
  set (UFState.mk s' h)
  return r

def find1 (s : UFState.Raw) (h : Acyclic s.parent) (t : Term) : Term × UFState.Raw :=
  go t
  where go t :=
    match hpar : s.parent[t]? with
    | none => (t, s)
    | some p =>
      let (r, s') := go p -- (match h with | Acc.intro _ ih => ih p hpar)
      (r, { s' with parent := s'.parent.insert t r })
  decreasing_by sorry

def find2 (s : UFState.Raw) (h : Acyclic s.parent) (t : Term) : Term × UFState.Raw :=
  go t (h.apply t)
  where go t (h : Acc (AncestorRel s.parent) t) :=
    match hpar : s.parent[t]? with
    | none => (t, s)
    | some p =>
      let (r, s') := go p (match h with | Acc.intro _ ih => ih p hpar)
      (r, { s' with parent := s'.parent.insert t r })

#check Lean.Parser.ParserFn
abbrev UFM := StateM UFState

def find' (t : Term) (s : UFState) : Term × UFState :=
  match s.parent[t]? with
  | none => (t, s)
  | some p =>
    let (r, s') := find' p s
    (r, { s' with parent := s'.parent.insert t r, parent_wf := sorry })

def union (t1 t2 : Term) : CC Unit := do
  let r1 ← find t1
  let r2 ← find t2
  if r1 != r2 then
    modify fun s => { s with parent := s.parent.insert r1 r2 }

def numReprs : CC Nat := do
  let s ← get
  let candidates := s.parent.values
  return candidates.filter (s.parent[·]? == none) |>.length

--theorem union_decreases {s} (t1 t2 : Term) (h : (.run s).1) :
--    ((do if (← find t1) != (← find t2) then union t1 t2 else return) s).2).1 < (numReprs s).1 := by
--  simp[numReprs, union, h]

def add_use (arg : Term) (app : Term) : CC Unit := do
  let rep ← find arg
  modify fun s =>
    let existing := s.uses.getD rep []
    { s with uses := s.uses.insert rep (app :: existing) }

partial def add_term (t : Term) : CC Unit := do
  match t with
  | var _ => return ()
  | app f args =>
    args.forM add_term
    args.forM (fun arg => add_use arg t)
    let canon_args ← args.mapM find
    let canon_app := app f canon_args
    union t canon_app

def assert_eq (t1 t2 : Term) : StateM UFState Unit := do
  let r1 ← find t1
  let r2 ← find t2
  if r1 != r2 then
    union r1 r2
    let s ← get
    let uses1 := s.uses.getD r1 []
    let uses2 := s.uses.getD r2 []
    -- Try to merge uses of r1 and r2 that might now be congruent
    for u1 in uses1, u2 in uses2 do
      match u1, u2 with
      | app f1 args1, app f2 args2 =>
        if f1 == f2 && (← args1.zip args2 |>.allM (λ (a, b) => do return ((← find a) == (← find b)))) then
          assert_eq u1 u2
      | _, _ => pure ()
termination_by numReprs

-- Example usage

def example : CC Unit := do
  let a := var "a"
  let b := var "b"
  let f := fun x => app "f" [x]
  add_term (f a)
  add_term (f b)
  assert_eq a b
  let r1 ← find (f a)
  let r2 ← find (f b)
  IO.println s!"f(a) rep: {r1}, f(b) rep: {r2}, equal: {r1 == r2}"

#eval example.run' {}
