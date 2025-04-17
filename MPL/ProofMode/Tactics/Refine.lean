import MPL.ProofMode.Focus
import MPL.ProofMode.Patterns.MRefine
import MPL.ProofMode.Tactics.Assumption
import MPL.ProofMode.Tactics.Exact

namespace MPL.ProofMode.Tactics
open MPL.ProofMode.Patterns
open Lean Elab Tactic Meta

def patAsTerm (pat : MRefinePat) (expected : Option Expr := none) : OptionT TacticM Expr := do
  match pat with
  | .pure t => elabTerm t expected
  | .one name =>
    if let `(binderIdent| $name:ident) := name then
      elabTerm (← `($name)) expected
    else failure
  | _ => failure

partial def mRefineCore (goal : MGoal) (pat : MRefinePat) (k : MGoal → TSyntax ``binderIdent → TacticM Expr) : TacticM Expr := do
  match pat with
  | .stateful name => liftMetaM do
    match name with
    | `(binderIdent| $name:ident) => do
      let some prf ← goal.exact (← `($name)) | throwError "unknown hypothesis '{name}'"
      return prf
    | _ => do
      let some prf ← goal.assumption | throwError "could not solve {goal.target} by assumption"
      return prf
  | .pure t => do
    goal.exactPure t
  | .one name =>
      if let `(binderIdent| $id:ident) := name then
        mRefineCore goal (.pure (← `($id))) k <|> mRefineCore goal (.stateful name) k
      else
        mRefineCore goal (.stateful name) k
  | .hole name => k goal name
  | .tuple [] => throwUnsupportedSyntax
  | .tuple [p] => mRefineCore goal p k
  | .tuple (p::ps) => do
    let T ← whnfR goal.target
    if let some (σs, T₁, T₂) := parseAnd? T.consumeMData then
      let prf₁ ← mRefineCore { goal with target := T₁ } p k
      let prf₂ ← mRefineCore { goal with target := T₂ } (.tuple ps) k
      return mkApp6 (mkConst ``SPred.and_intro) σs goal.hyps T₁ T₂ prf₁ prf₂
    else if let some (α, σs, ψ) := T.app3? ``SPred.exists then
      let some witness ← patAsTerm p (some α) | throwError "pattern does not elaborate to a term to instantiate ψ"
      let prf ← mRefineCore { goal with target := ψ.betaRev #[witness] } (.tuple ps) k
      let u ← getLevel α
      return mkApp6 (mkConst ``SPred.exists_intro' [u]) α σs goal.hyps ψ witness prf
    else throwError "Neither a conjunction nor an existential quantifier {goal.target}"

elab "mrefine" pat:mrefinePat : tactic => do
  let pat ← liftMacroM <| MRefinePat.parse pat
  let (mvar, goal) ← mStart (← getMainGoal)
  mvar.withContext do

  let goals ← IO.mkRef #[]
  let prf ← mRefineCore goal pat fun goal name => do
    let m ← mkFreshExprSyntheticOpaqueMVar goal.toExpr name.raw.getId
    goals.modify (·.push m.mvarId!)
    return m
  mvar.assign prf
  replaceMainGoal (← goals.get).toList

macro "mexists" args:term,+ : tactic => do
  let pats ← args.getElems.mapM fun t => `(mrefinePat| ⌜$t⌝)
  let pat ← pats.foldrM (fun pat acc => `(mrefinePat| ⟨$pat, $acc⟩)) (← `(mrefinePat| ?_))
  `(tactic| (mrefine $pat; try massumption))
