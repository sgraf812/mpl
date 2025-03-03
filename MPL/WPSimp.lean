import Lean
import MPL.SimpAttr

namespace MPL

open Lean Parser Meta Elab Tactic

my_register_simp_attr wp_simp

def getWPSimpTheorems : CoreM SimpTheorems :=
  wp_simp_ext.getTheorems

syntax (name := wp_simp) "wp_simp" optConfig (discharger)? (&" only")?
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")? (location)? : tactic

@[tactic wp_simp] def evalWPSimp : Tactic := fun stx => withMainContext do withSimpDiagnostics do
  let { ctx, simprocs, dischargeWrapper } ← mkSimpContext stx (eraseLocal := false) (simpTheorems := getWPSimpTheorems)
  let stats ← dischargeWrapper.with fun discharge? =>
    simpLocation ctx simprocs discharge? (expandOptLocation stx[5])
  if tactic.simp.trace.get (← getOptions) then
    traceSimpCall stx stats.usedTheorems
  return stats.diag


/-
-- Auxiliary attribute for builtin `wp_simp` simprocs.
--
-- syntax (name := wp_simpProcBuiltinAttr) "builtin_wp_simp_proc" (Tactic.simpPre <|> Tactic.simpPost)? : attr
--
-- macro_rules
--   | `($[$doc?:docComment]? $kind:attrKind builtin_simproc $[$pre?]? [wp_simp] $n:ident ($pattern:term) := $body) => do
--     `($[$doc?:docComment]? builtin_simproc_decl $n ($pattern) := $body
--       attribute [$kind builtin_wp_simp_proc $[$pre?]?] $n)

-- my_register_simp_attr wp_simp
--

-- private def addBuiltin (declName : Name) (stx : Syntax) (addDeclName : Name) : AttrM Unit := do
--   let post := if stx[1].isNone then true else stx[1][0].getKind == ``Lean.Parser.Tactic.simpPost
--   let procExpr ← match (← getConstInfo declName).type with
--     | .const ``Simproc _  => pure <| mkApp3 (mkConst ``Sum.inl [0, 0]) (mkConst ``Simproc) (mkConst ``DSimproc) (mkConst declName)
--     | _ => throwError "unexpected type at wp_simp simproc"
--   let val := mkAppN (mkConst addDeclName) #[toExpr declName, toExpr post, procExpr]
--   let initDeclName ← mkFreshUserName (declName ++ `declare)
--   declareBuiltin initDeclName val

--def addVCGenProcBuiltinAttr (declName : Name) (post : Bool) (proc : Sum Simproc DSimproc) : IO Unit :=
--  addSimprocBuiltinAttrCore builtinVCGenSimprocsRef declName post proc

-- initialize
--   registerBuiltinAttribute {
--     ref             := by exact decl_name%
--     name            := `wpSimpProcBuiltinAttr
--     descr           := "Builtin wp_simp simproc"
--     applicationTime := AttributeApplicationTime.afterCompilation
--     erase           := fun _ => throwError "Not implemented yet, [-builtin_wp_simp_proc]"
--     add             := fun declName stx _ => addBuiltin declName stx ``addVCGenProcBuiltinAttr
--   }
-/
