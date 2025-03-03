import Lean

namespace MPL.SimpAttr

-- TODO: Upstream

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
