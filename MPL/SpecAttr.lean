/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
import Lean
import MPL.Triple
import MPL.Util.Trace

namespace MPL

open Lean Meta

initialize registerTraceClass `mpl.spec.attr (inherited := true)

structure SpecTheorem where
  keys : Array DiscrTree.Key
  /-- Level params of the theorem definition. -/
  levelParams : List Name
  /--
  Expr key tested for matching, in ∀-quantified form.
  `keys = (← mkPath (← forallMetaTelescope prog).2.2)`.
  -/
  prog : Expr
  /-- The name of the theorem that proves the spec. -/
  proof : Name
  /--
  If `etaPotential` is non-zero, then the precondition contains meta variables that can be
  instantiated after applying `mintro ∀s` `etaPotential` many times.
  -/
  etaPotential : Nat := 0
  priority : Nat  := eval_prio default -- TODO: unused
  origin : Origin
  /-- `rfl` is true if `proof` is by `SPred.entails.rfl`. -/
  rfl : Bool
  deriving Inhabited, BEq

abbrev SpecEntry := SpecTheorem

structure SpecTheorems where
  specs : DiscrTree SpecTheorem := DiscrTree.empty
  deriving Inhabited

abbrev SpecExtension := SimpleScopedEnvExtension SpecEntry SpecTheorems

private partial def computeEtaPotentialForInstantiation (e : Expr) : MetaM Nat :=
  Int.toNat <$> go e 0 -- Int.toNat turns any negative balance into 0, as required
  where
    noMVar := -10000000000 -- "640k ought to be enough for anybody"
    go (e : Expr) (balance : Int) : MetaM Int := do
      if !e.hasExprMVar then return noMVar
      match e with
      | .mdata _ e => go e balance
      | .app .. =>
        if e.isAppOf ``SPred.and || e.isAppOf ``SPred.or then
          let P := e.getArg! 1
          let Q := e.getArg! 2
          let balance := balance - (e.getAppNumArgs - 3)
          return ← max <$> go P balance <*> go Q balance
        if e.isAppOf ``And || e.isAppOf ``Or then
          let P := e.getArg! 0
          let Q := e.getArg! 1
          let balance := balance - (e.getAppNumArgs - 2)
          return ← max <$> go P balance <*> go Q balance
        if e.isAppOf ``SVal.curry then
          let P := e.getArg! 1
          let Q := e.getArg! 2
          let balance := balance - (e.getAppNumArgs - 3)
          return ← max <$> go P balance <*> go Q balance
        if let some (_, lhs, rhs) := e.eq? then
          if lhs.getAppFn'.isMVar || rhs.getAppFn'.isMVar then
            return balance
          return noMVar
        go e.getAppFn (balance - e.getAppNumArgs)
      | .lam .. =>
        lambdaTelescope e fun xs e => go e (balance + xs.size)
      | .proj .. =>
        match (← reduceProj? e) with
        | some e' => go e' balance
        | none    => return noMVar
      | .letE .. => lambdaLetTelescope e fun _ e => go e balance
      | .forallE .. => return noMVar -- Not sure what to do here
      | .mvar .. => return noMVar -- NB: A likely SPred-valued mvar. Not the case we look for!
      | .lit .. | .fvar .. | .bvar .. | .sort .. | .const .. =>
        unreachable!

private partial def countBVarDependentMVars (e : Expr) : MetaM Nat := do
  if !e.hasExprMVar then return 0
  match e with
  | .app f a =>
    if let some (_, lhs, rhs) := e.eq? then
      if lhs.getAppFn'.isMVar && rhs.hasLooseBVars then return 1
      if rhs.getAppFn'.isMVar && lhs.hasLooseBVars then return 1
      return ← (· + ·) <$> countBVarDependentMVars lhs <*> countBVarDependentMVars rhs
    return ← (· + ·) <$> countBVarDependentMVars f <*> countBVarDependentMVars a
  | .mdata _ e => countBVarDependentMVars e
  | .lam _ ty b _ => (· + ·) <$> countBVarDependentMVars ty <*> countBVarDependentMVars b
  | .letE _ ty v b _ => (· + · + ·) <$> countBVarDependentMVars ty <*> countBVarDependentMVars v <*> countBVarDependentMVars b
  | .forallE _ ty b _ => (· + ·) <$> countBVarDependentMVars ty <*> countBVarDependentMVars b
  | .proj _ _ e => countBVarDependentMVars e
  | .mvar .. => return 0
  | .lit .. | .fvar .. | .bvar .. | .sort .. | .const .. => return 0


private partial def computeEtaPotentialForInstantiation2 (σs : Expr) (e : Expr) : MetaM Nat :=
  withNewMCtxDepth do
  withConfig (fun cfg => { cfg with iota := true, beta := true, zeta := true, zetaDelta := true, proj := .yesWithDelta }) do
  let ctx ← Simp.Context.mkDefault
  logInfo s!"{σs}"
  let mut σs ← whnfR σs
  let mut e := e
  let mut n : Nat := 0
  let mut lastSuccess := 0
  let mut boundAssignments ← countBVarDependentMVars e
  logInfo m!"comp σs: {σs}"
  while σs.isAppOfArity ``List.cons 3 do
    let σ := σs.getArg! 1
    logInfo m!"next {σ}, {n}: e: {e}"
    let s ← mkFreshExprMVar σ
    e := e.beta #[s]
    let (r, _) ← simp e ctx
    e := r.expr
    let count ← countBVarDependentMVars e
    logInfo m!"count {count}, {boundAssignments}"
    if count < boundAssignments then
      lastSuccess := n
      boundAssignments := count
    n := n+1
    σs ← whnfR (σs.getArg! 2)
  return lastSuccess

private def mkSpecTheorem (origin : Origin) (type : Expr) (levelParams : List Name) (proof : Name) (prio : Nat) : MetaM SpecTheorem := do
  -- cf. mkSimpTheoremCore
  let type ← instantiateMVars type
  withNewMCtxDepth do
  let (xs, _, type) ← forallMetaTelescopeReducing type
  let type ← whnfR type
  let_expr Triple _m ps _inst _α prog P _Q := type
    | throwError "unexpected kind of spec theorem; not a triple{indentExpr type}"
  let f := prog.getAppFn'
  unless f.isConst do throwError s!"not an application of a constant: {prog}"
  let keys ← DiscrTree.mkPath prog (noIndexAtArgs := false)
  let etaPotential ← computeEtaPotentialForInstantiation2 (mkApp (mkConst ``PostShape.args) ps) P
  logInfo m!"Eta potential of {P}: {etaPotential}"
  -- logInfo m!"mkSpecTheorem: {keys}, proof: {proof}"
  return { keys, levelParams, prog := (← mkForallFVars xs prog), proof, etaPotential, origin, rfl := false, priority := prio }

private def mkSpecTheoremFromConst (declName : Name) (prio : Nat) : MetaM SpecTheorem := do
  -- cf. mkSimpTheoremsFromConst
  let cinfo ← getConstInfo declName
  let us := cinfo.levelParams.map mkLevelParam
  let origin := Origin.decl declName
  let val := mkConst declName us
  withSimpGlobalConfig do -- sounds like a good default here,
    let type ← inferType val
    unless (← isProp type) do
      throwError "invalid 'spec', proposition expected{indentExpr type}"
    mkSpecTheorem origin type cinfo.levelParams declName prio

def addSpecTheoremEntry (d : SpecTheorems) (e : SpecTheorem) : SpecTheorems :=
  { d with specs := d.specs.insertCore e.keys e }

def addSpecTheorem (ext : SpecExtension) (declName : Name) (prio : Nat) (attrKind : AttributeKind) : MetaM Unit := do
  let thm ← mkSpecTheoremFromConst declName prio
  -- logInfo m!"addSpecTheorem: {thm.keys}, proof: {thm.proof}"
  -- let thms := ext.getState (← getEnv)
  -- let grps := thms.specs.values.groupByKey (·.keys)
  -- logInfo m!"thms: {grps.map (fun k v => v.map (·.proof)) |>.toList}"
  ext.add thm attrKind

def mkSpecExt : IO SpecExtension :=
  registerSimpleScopedEnvExtension {
    name     := `specMap
    initial  := {}
    addEntry := addSpecTheoremEntry
  }

def mkSpecAttr (ext : SpecExtension) : IO Unit :=
  registerBuiltinAttribute {
    name  := `spec
    descr := "Marks theorems to use with the `mspec` and `mvcgen` tactics"
    -- applicationTime := AttributeApplicationTime.afterCompilation -- this seems unnecessarily conservative?
    applicationTime := AttributeApplicationTime.afterTypeChecking
    add   := fun declName stx attrKind => do
      let go : MetaM Unit := do
        let info ← getConstInfo declName
        let prio ← Attribute.Builtin.getPrio stx
        if (← isProp info.type) then
          addSpecTheorem ext declName prio attrKind
        -- TODO: add unfold rules
        -- else if info.hasValue then
        --   if (← SimpTheorems.ignoreEquations declName) then
        --     ext.add (SimpEntry.toUnfold declName) attrKind
        --   else if let some eqns ← getEqnsFor? declName then
        --     for eqn in eqns do
        --       addSimpTheorem ext eqn post (inv := false) attrKind prio
        --     ext.add (SimpEntry.toUnfoldThms declName eqns) attrKind
        --     if (← SimpTheorems.unfoldEvenWithEqns declName) then
        --       ext.add (SimpEntry.toUnfold declName) attrKind
        --   else
        --     ext.add (SimpEntry.toUnfold declName) attrKind
        else
          throwError "invalid 'spec', it is not a proposition" -- nor a definition (to unfold)"
      discard <| go.run {} {}
      -- TODO: add erase
  }

initialize specAttr : SpecExtension ← do
  let ext ← mkSpecExt
  mkSpecAttr ext
  return ext

def SpecExtension.getTheorems (ext : SpecExtension) : CoreM SpecTheorems :=
  return ext.getState (← getEnv)

def getSpecTheorems : CoreM SpecTheorems :=
  specAttr.getTheorems

end MPL
