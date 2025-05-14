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
  proof : Name -- TODO: Could be Expr, as for `SimpTheorem`
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

private def mkSpecTheorem (origin : Origin) (type : Expr) (proof : Name) (prio : Nat) : MetaM SpecTheorem := do
  -- cf. mkSimpTheoremCore
  let type ← instantiateMVars type
  withNewMCtxDepth do
  let (_, _, type) ← forallMetaTelescopeReducing type
  let type ← whnfR type
  let_expr Triple _m _ps _inst _α prog _P _Q := type
    | throwError "unexpected kind of spec theorem; not a triple{indentExpr type}"
  let f := prog.getAppFn'
  unless f.isConst do throwError s!"not an application of a constant: {prog}"
  let keys ← DiscrTree.mkPath prog (noIndexAtArgs := false)
  return { keys, proof, origin, rfl := false, priority := prio }

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
    mkSpecTheorem origin type declName prio

def addSpecTheorem (ext : SpecExtension) (declName : Name) (prio : Nat) (attrKind : AttributeKind) : MetaM Unit := do
  ext.add (← mkSpecTheoremFromConst declName prio) attrKind

def addSpecTheoremEntry (d : SpecTheorems) (e : SpecTheorem) : SpecTheorems :=
  { d with specs := d.specs.insertCore e.keys e }

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
