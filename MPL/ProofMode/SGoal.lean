import Lean
import MPL.SProp
open Lean Elab Meta

namespace MPL.ProofMode

class PropAsEntails (φ : Prop) {σs : outParam (List Type)} (P : outParam (SProp σs)) : Prop where
  prop_as_entails : φ ↔ ⊢ₛ P

instance : PropAsEntails (⊢ₛ P) P where
  prop_as_entails := Iff.rfl

instance : PropAsEntails (P ⊢ₛ Q) sprop(P → Q) where
  prop_as_entails := (SProp.entails_true_intro P Q).symm

theorem start_entails (φ : Prop) [PropAsEntails φ P] : (⊢ₛ P) → φ :=
  PropAsEntails.prop_as_entails.mpr

@[match_pattern] def sgoalAnnotation := `sgoal
@[match_pattern] def nameAnnotation := `name
@[match_pattern] def uniqAnnotation := `uniq

structure Hyp where
  name : Name
  uniq : Name
  p : Expr

def parseHyp? : Expr → Option Hyp
  | .mdata ⟨[(nameAnnotation, .ofName name), (uniqAnnotation, .ofName uniq)]⟩ p =>
    some ⟨name, uniq, p⟩ -- NB: mdatas are transparent to SubExpr; hence no pos.push
  | _ => none

def Hyp.toExpr (hyp : Hyp) : Expr :=
  .mdata ⟨[(nameAnnotation, .ofName hyp.name), (uniqAnnotation, .ofName hyp.uniq)]⟩ hyp.p

-- set_option pp.all true in
-- #check ⌜True⌝
def emptyHyp (σs : Expr) : Expr := -- ⌜True⌝ standing in for an empty conjunction of hypotheses
  mkApp2 (mkConst ``SProp.idiom) σs <| mkLambda `escape .default (mkApp (mkConst ``SVal.EscapeFun) σs) (mkConst ``True)
def parseEmptyHyp? : Expr → Option Expr
  | mkApp2 (.const ``SProp.idiom _) σs (.lam _ _ (.const ``True _) _) => some σs
  | _ => none

def pushLeftConjunct (pos : SubExpr.Pos) : SubExpr.Pos :=
  pos.pushNaryArg 3 1

def pushRightConjunct (pos : SubExpr.Pos) : SubExpr.Pos :=
  pos.pushNaryArg 3 2

/-- Combine two hypotheses into a conjunction.
Precondition: Neither `lhs` nor `rhs` is empty (`parseEmptyHyp?`). -/
def mkAnd! (σs lhs rhs : Expr) : Expr :=
  mkApp3 (mkConst ``SProp.and) σs lhs rhs

/-- Smart constructor that cancels away empty hypotheses,
along with a proof that `lhs ∧ rhs ⊣⊢ₛ result`. -/
def mkAnd (σs lhs rhs : Expr) : Expr × Expr :=
  if let some _ := parseEmptyHyp? lhs then
    (rhs, mkApp2 (mkConst ``SProp.true_and) σs rhs)
  else if let some _ := parseEmptyHyp? rhs then
    (lhs, mkApp2 (mkConst ``SProp.and_true) σs lhs)
  else
    let result := mkAnd! σs lhs rhs
    (result, mkApp2 (mkConst ``SProp.bientails.refl) σs result)

def parseAnd? (e : Expr) : Option (Expr × Expr × Expr) :=
  e.app3? ``SProp.and

structure SGoal where
  σs : Expr -- Q(List Type)
  hyps : Expr -- A conjunction of hypotheses in `SProp σs`, each carrying a name and uniq as metadata (`parseHyp?`)
  target : Expr -- Q(SProp $σs)

def parseSGoal? (expr : Expr) : Option SGoal := do
  let .mdata ⟨[(sgoalAnnotation, .ofBool true)]⟩ e := expr | none
  let some (σs, hyps, target) := e.app3? ``SProp.entails | none
  some { σs, hyps, target }

def SGoal.strip (goal : SGoal) : Expr := -- omits the .mdata wrapper
  mkApp3 (mkConst ``SProp.entails) goal.σs goal.hyps goal.target

/-- Roundtrips with `parseSGoal?`. -/
def SGoal.toExpr (goal : SGoal) : Expr :=
  .mdata ⟨[(sgoalAnnotation, .ofBool true)]⟩ goal.strip

/-- O(n), but shortcuts. -/
partial def SGoal.findHyp? (goal : SGoal) (name : Name) : Option (SubExpr.Pos × Hyp) := go goal.hyps SubExpr.Pos.root
  where
    go (e : Expr) (p : SubExpr.Pos) : Option (SubExpr.Pos × Hyp) := do
      if let some hyp := parseHyp? e then
        if hyp.name = name then
          return (p, hyp)
        else
          none
      else if let some (_, lhs, rhs) := parseAnd? e then
        go lhs (pushLeftConjunct p) <|> go rhs (pushRightConjunct p)
      else if let some _ := parseEmptyHyp? e then
        none
      else
        panic! "SGoal.findHyp?: hypothesis without proper metadata: {e}"

/-- O(n). Slower than a single `findHyp?`, but faster for multiple queries.
Modifications of the hypotheses invalidate the index. -/
partial def SGoal.buildHypIndex (goal : SGoal) : Std.HashMap Name (SubExpr.Pos × Hyp) :=
  go goal.hyps SubExpr.Pos.root Std.HashMap.empty
  where
    go (e : Expr) (p : SubExpr.Pos) (acc : Std.HashMap Name (SubExpr.Pos × Hyp)) : Std.HashMap Name (SubExpr.Pos × Hyp) :=
      if let some hyp := parseHyp? e then
        acc.insert hyp.name (p, hyp)
      else if let some (_, lhs, rhs) := parseAnd? e then
        go lhs (pushLeftConjunct p) (go rhs (pushRightConjunct p) acc)
      else if let some _ := parseEmptyHyp? e then
        acc
      else
        panic! "SGoal.buildHypIndex: hypothesis without proper metadata: {e}"

def getFreshHypName : TSyntax ``binderIdent → CoreM (Name × Syntax)
  | `(binderIdent| $name:ident) => pure (name.getId, name)
  | stx => return (← mkFreshUserName `h, stx)

/-- This is only used for display purposes, so that we can render context variables that appear
to have type `A : PROP` even though `PROP` is not a type. -/
def HypMarker {σs : List Type} (_A : SProp σs) : Prop := True

def addLocalVarInfo (stx : Syntax) (lctx : LocalContext)
    (expr : Expr) (expectedType? : Option Expr) (isBinder := false) : MetaM Unit := do
  Elab.withInfoContext' (pure ())
    (fun _ =>
      return .inl <| .ofTermInfo
        { elaborator := .anonymous, lctx, expr, stx, expectedType?, isBinder })
    (return .ofPartialTermInfo { elaborator := .anonymous, lctx, stx, expectedType? })

def addHypInfo (stx : Syntax) (name uniq : Name) (p : Expr /-Q(SProp $σs)-/)
    (isBinder := false) : MetaM Unit := do
  let lctx ← getLCtx
  let .app (.const ``SProp []) σs ← inferType p | throwError "addHypInfo: expected an SProp {p}"
  let p := mkApp2 (mkConst ``HypMarker) σs p
  addLocalVarInfo stx (lctx.mkLocalDecl ⟨uniq⟩ name p) (.fvar ⟨uniq⟩) p isBinder

def SGoal.findWithInfo (goal : SGoal) (name : Ident) : MetaM (SubExpr.Pos × Name) := do
  let some (p, h) := goal.findHyp? name.getId | throwError "unknown hypothesis {name}"
  addHypInfo name name.getId h.uniq h.p
  pure (p, h.uniq)
