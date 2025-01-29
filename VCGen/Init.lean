import Lean

namespace VCGen

open Lean Meta Simp

macro (name := myRegisterSimpAttr) doc:(docComment)?
  "my_register_simp_attr" id:ident : command => do
  let str := id.getId.toString
  let extName := mkIdentFrom id (id.getId.appendAfter "_ext");
  let extProcName := mkIdentFrom id (id.getId.appendAfter "_proc_ext");
  let idParser := mkIdentFrom id (`Parser.Attr ++ id.getId)
  let descr := quote ((doc.map (·.getDocString) |>.getD s!"simp set for {id.getId.toString}").removeLeadingSpaces)
  let procId := mkIdentFrom id (simpAttrNameToSimprocAttrName id.getId)
  let procStr := procId.getId.toString
  let procIdParser := mkIdentFrom procId (`Parser.Attr ++ procId.getId)
  let procDescr := quote s!"simproc set for {procId.getId.toString}"
  -- TODO: better docDomment for simprocs
  `($[$doc:docComment]? initialize $(extName) : SimpExtension ← registerSimpAttr $(quote id.getId) $descr $(quote id.getId)
    $[$doc:docComment]? syntax (name := $idParser:ident) $(quote str):str (Parser.Tactic.simpPre <|> Parser.Tactic.simpPost)? patternIgnore("← " <|> "<- ")? (prio)? : attr
    /-- Simplification procedure -/
    initialize $(extProcName) : SimprocExtension ← registerSimprocAttr $(quote procId.getId) $procDescr none $(quote procId.getId)
    /-- Simplification procedure -/
    syntax (name := $procIdParser:ident) $(quote procStr):str (Parser.Tactic.simpPre <|> Parser.Tactic.simpPost)? : attr)

my_register_simp_attr vc_gen

def getVCGenTheorems : CoreM SimpTheorems :=
  vc_gen_ext.getTheorems

private def addBuiltin (declName : Name) (stx : Syntax) (addDeclName : Name) : AttrM Unit := do
  let post := if stx[1].isNone then true else stx[1][0].getKind == ``Lean.Parser.Tactic.simpPost
  let procExpr ← match (← getConstInfo declName).type with
    | .const ``Simproc _  => pure <| mkApp3 (mkConst ``Sum.inl [0, 0]) (mkConst ``Simproc) (mkConst ``DSimproc) (mkConst declName)
    | _ => throwError "unexpected type at vcgen simproc"
  let val := mkAppN (mkConst addDeclName) #[toExpr declName, toExpr post, procExpr]
  let initDeclName ← mkFreshUserName (declName ++ `declare)
  declareBuiltin initDeclName val

--def addVCGenProcBuiltinAttr (declName : Name) (post : Bool) (proc : Sum Simproc DSimproc) : IO Unit :=
--  addSimprocBuiltinAttrCore builtinVCGenSimprocsRef declName post proc

-- initialize
--   registerBuiltinAttribute {
--     ref             := by exact decl_name%
--     name            := `vcgenProcBuiltinAttr
--     descr           := "Builtin vcgen simproc"
--     applicationTime := AttributeApplicationTime.afterCompilation
--     erase           := fun _ => throwError "Not implemented yet, [-builtin_vcgen_proc]"
--     add             := fun declName stx _ => addBuiltin declName stx ``addVCGenProcBuiltinAttr
--   }
