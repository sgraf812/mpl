import Lean
import MPL.Triple

namespace MPL

open Lean Meta

/- Discrimination trees map expressions to values. When storing an expression
   in a discrimination tree, the expression is first converted to an array
   of `DiscrTree.Key`, which are the keys actually used by the discrimination
   trees. The conversion operation is monadic, however, and extensions require
   all the operations to be pure. For this reason, in the state extension, we
   store the keys from *after* the transformation (i.e., the `DiscrTreeKey`
   below). The transformation itself can be done elsewhere.
 -/
abbrev DiscrTreeKey := Array DiscrTree.Key

abbrev DiscrTreeExtension (α : Type) :=
  SimplePersistentEnvExtension (DiscrTreeKey × α) (DiscrTree α)

def mkDiscrTreeExtension [Inhabited α] [BEq α] (name : Name := by exact decl_name%) :
  IO (DiscrTreeExtension α) :=
  registerSimplePersistentEnvExtension {
    name          := name,
    addImportedFn := fun a => a.foldl (fun s a => a.foldl (fun s (k, v) => s.insertCore k v) s) DiscrTree.empty,
    addEntryFn    := fun s n => s.insertCore n.1 n.2 ,
  }

-- spec attribute
structure SpecAttr where
  attr : AttributeImpl
  ext  : DiscrTreeExtension Name
  deriving Inhabited

/-- For the attributes

    If we apply an attribute to a definition in a group of mutually recursive definitions
    (say, to `foo` in the group [`foo`, `bar`]), the attribute gets applied to `foo` but also to
    the recursive definition which encodes `foo` and `bar` (Lean encodes mutually recursive
    definitions in one recursive definition, e.g., `foo._mutual`, before deriving the individual
    definitions, e.g., `foo` and `bar`, from this one). This definition should be named `foo._mutual`
    or `bar._mutual`, and we generally want to ignore it.

    TODO: same problem happens if we use decreases clauses, etc.

    Below, we implement a small utility to do so.
  -/
def attrIgnoreAuxDef (name : Name) (default : AttrM α) (x : AttrM α) : AttrM α := do
  -- TODO: this is a hack
  if let .str _ "_mutual" := name then
--    trace[Utils] "Ignoring a mutually recursive definition: {name}"
    default
  else if let .str _ "_unary" := name then
--    trace[Utils] "Ignoring a unary def: {name}"
    default
  else
    -- Normal execution
    x

initialize registerTraceClass `mpl (inherited := true)

def getSpecKey (ty : Expr) : MetaM Expr := do
  let (_xs, _bis, body) ← forallMetaTelescope ty
  let_expr triple _m _ps _inst _α x _P _Q := body | throwError s!"not a triple: {body}"
  if x.getAppFn'.isConst then
    return x
  else
    throwError s!"not an application of a constant: {x}"

/- The persistent map from expressions to pspec theorems. -/
initialize specAttr : SpecAttr ← do
  let ext ← mkDiscrTreeExtension `specMap
  let attrImpl : AttributeImpl := {
    name := `spec
    descr := "Marks theorems to use with the `xapp` tactic"
    add := fun thName stx attrKind => do
      Attribute.Builtin.ensureNoArgs stx
      -- TODO: use the attribute kind
      unless attrKind == AttributeKind.global do
        throwError "invalid attribute 'spec', must be global"
      -- Lookup the theorem
      let env ← getEnv
      -- Ignore some auxiliary definitions (see the comments for attrIgnoreMutRec)
      attrIgnoreAuxDef thName (pure ()) do
        trace[mpl] "Registering spec theorem for {thName}"
        let thDecl := env.constants.find! thName
        let fKey ← MetaM.run' (do
          let mut ty := thDecl.type
          trace[mpl] "Theorem: {ty}"
          -- Normalize to eliminate the let-bindings
--          ty ← zetaReduce ty
--          trace[mpl] "Theorem after normalization (to eliminate the let bindings): {ty}"
          let fExpr ← getSpecKey ty
          trace[mpl] "Registering spec theorem for expr: {fExpr}"
          -- Convert the function expression to a discrimination tree key
          DiscrTree.mkPath fExpr)
        let env := ext.addEntry env (fKey, thName)
        setEnv env
        trace[mpl] "Saved the environment"
        pure ()
  }
  registerBuiltinAttribute attrImpl
  pure { attr := attrImpl, ext := ext }

def SpecAttr.find? (s : SpecAttr) (e : Expr) : MetaM (Array Name) := do
  (s.ext.getState (← getEnv)).getMatch e

def SpecAttr.getState (s : SpecAttr) : MetaM (DiscrTree Name) := do
  pure (s.ext.getState (← getEnv))

def showStoredSpec : MetaM Unit := do
  let st ← specAttr.getState
  -- TODO: how can we iterate over (at least) the values stored in the tree?
  --let s := st.toList.foldl (fun s (f, th) => f!"{s}\n{f} → {th}") f!""
  let s := f!"{st}"
  IO.println s

end MPL
