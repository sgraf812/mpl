import Lean
import MPL.SPred
open Lean Elab Meta

namespace MPL.ProofMode

class PropAsEntails (φ : Prop) {σs : outParam (List Type)} (P : outParam (SPred σs)) : Prop where
  prop_as_entails : φ ↔ ⊢ₛ P

instance : PropAsEntails (⊢ₛ P) P where
  prop_as_entails := Iff.rfl

instance : PropAsEntails (P ⊢ₛ Q) spred(P → Q) where
  prop_as_entails := (SPred.entails_true_intro P Q).symm

theorem start_entails (φ : Prop) [PropAsEntails φ P] : (⊢ₛ P) → φ :=
  PropAsEntails.prop_as_entails.mpr

/-- Tautology in `SPred` as a definition. -/
abbrev _root_.MPL.SPred.tautological {σs : List Type} (Q : SPred σs) : Prop := ⊢ₛ Q

@[match_pattern] def mgoalAnnotation := `mgoal
@[match_pattern] def nameAnnotation := `name

structure Hyp where
  name : Name
  p : Expr

def parseHyp? : Expr → Option Hyp
  | .mdata ⟨[(nameAnnotation, .ofName name)]⟩ p =>
    some ⟨name, p⟩ -- NB: mdatas are transparent to SubExpr; hence no pos.push
  | _ => none

def Hyp.toExpr (hyp : Hyp) : Expr :=
  .mdata ⟨[(nameAnnotation, .ofName hyp.name)]⟩ hyp.p

-- set_option pp.all true in
-- #check ⌜True⌝
def emptyHyp (σs : Expr) : Expr := -- ⌜True⌝ standing in for an empty conjunction of hypotheses
  mkApp2 (mkConst ``SPred.idiom) σs <| mkLambda `escape .default (mkApp (mkConst ``SVal.EscapeFun) σs) (mkConst ``True)
def parseEmptyHyp? : Expr → Option Expr
  | mkApp2 (.const ``SPred.idiom _) σs (.lam _ _ (.const ``True _) _) => some σs
  | _ => none

def pushLeftConjunct (pos : SubExpr.Pos) : SubExpr.Pos :=
  pos.pushNaryArg 3 1

def pushRightConjunct (pos : SubExpr.Pos) : SubExpr.Pos :=
  pos.pushNaryArg 3 2

/-- Combine two hypotheses into a conjunction.
Precondition: Neither `lhs` nor `rhs` is empty (`parseEmptyHyp?`). -/
def mkAnd! (σs lhs rhs : Expr) : Expr :=
  mkApp3 (mkConst ``SPred.and) σs lhs rhs

/-- Smart constructor that cancels away empty hypotheses,
along with a proof that `lhs ∧ rhs ⊣⊢ₛ result`. -/
def mkAnd (σs lhs rhs : Expr) : Expr × Expr :=
  if let some _ := parseEmptyHyp? lhs then
    (rhs, mkApp2 (mkConst ``SPred.true_and) σs rhs)
  else if let some _ := parseEmptyHyp? rhs then
    (lhs, mkApp2 (mkConst ``SPred.and_true) σs lhs)
  else
    let result := mkAnd! σs lhs rhs
    (result, mkApp2 (mkConst ``SPred.bientails.refl) σs result)

def parseAnd? (e : Expr) : Option (Expr × Expr × Expr) :=
  e.app3? ``SPred.and

structure MGoal where
  σs : Expr -- Q(List Type)
  hyps : Expr -- A conjunction of hypotheses in `SPred σs`, each carrying a name and uniq as metadata (`parseHyp?`)
  target : Expr -- Q(SPred $σs)
  deriving Inhabited

def parseMGoal? (expr : Expr) : Option MGoal := do
  let .mdata ⟨[(mgoalAnnotation, .ofBool true)]⟩ e := expr | none
  let some (σs, hyps, target) := e.app3? ``SPred.entails | none
  some { σs, hyps, target }

def MGoal.strip (goal : MGoal) : Expr := -- omits the .mdata wrapper
  mkApp3 (mkConst ``SPred.entails) goal.σs goal.hyps goal.target

/-- Roundtrips with `parseMGoal?`. -/
def MGoal.toExpr (goal : MGoal) : Expr :=
  .mdata ⟨[(mgoalAnnotation, .ofBool true)]⟩ goal.strip

partial def MGoal.findHyp? (goal : MGoal) (name : Name) : Option (SubExpr.Pos × Hyp) := go goal.hyps SubExpr.Pos.root
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
        panic! "MGoal.findHyp?: hypothesis without proper metadata: {e}"

def MGoal.checkProof (goal : MGoal) (prf : Expr) (suppressWarning : Bool := false) : MetaM Unit := do
  check prf
  let prf_type ← inferType prf
  unless ← isDefEq goal.toExpr prf_type do
    throwError "MGoal.checkProof: the proof and its supposed type did not match.\ngoal:  {goal.toExpr}\nproof: {prf_type}"
  unless suppressWarning do
    logWarning m!"stray MGoal.checkProof {prf_type} {goal.toExpr}"

def getFreshHypName : TSyntax ``binderIdent → CoreM (Name × Syntax)
  | `(binderIdent| $name:ident) => pure (name.getId, name)
  | stx => return (← mkFreshUserName `h, stx)
