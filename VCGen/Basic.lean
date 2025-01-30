import Lean
import VCGen.Init

namespace VCGen

open Lean Parser Meta Elab Tactic

def Context.mkDefault : MetaM Simp.Context := do
  Simp.mkContext
    (config := {})
    (simpTheorems := #[(← getVCGenTheorems)])
    (congrTheorems := (← Meta.getSimpCongrTheorems))

section Parser

syntax (name := vc_gen) "vc_gen" optConfig (discharger)? (&" only")?
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")? (location)? : tactic

/--
Auxiliary attribute for builtin `vc_gen` simprocs.
-/
syntax (name := vc_genProcBuiltinAttr) "builtin_vc_gen_proc" (Tactic.simpPre <|> Tactic.simpPost)? : attr

macro_rules
  | `($[$doc?:docComment]? $kind:attrKind builtin_simproc $[$pre?]? [vc_gen] $n:ident ($pattern:term) := $body) => do
    `($[$doc?:docComment]? builtin_simproc_decl $n ($pattern) := $body
      attribute [$kind builtin_vc_gen_proc $[$pre?]?] $n)

-- macro_rules
--   | `(tactic| vc_gen $cfg:optConfig) => do
--     `(tactic| simp $cfg only [←LawfulMonad.bind_pure_comp, ←LawfulMonad.bind_map, vc_gen])

end Parser

section Elab

-- def vc_gen' (g : MVarId) (cfg : BVDecideConfig) : MetaM (Option MVarId) := do
--   withTraceNode `vc (fun _ => return "Generating verification conditions") do
--     return none

--@[tactic vc_gen]
--def evalVCGen : Tactic
--  | `(tactic| vc_gen $cfg:optConfig) => do
--    `(tactic| simp $cfg only [vc_gen])
--  | _ => throwUnsupportedSyntax

@[tactic vc_gen] def evalVCGen : Tactic := fun stx => withMainContext do withSimpDiagnostics do
  let { ctx, simprocs, dischargeWrapper } ← mkSimpContext stx (eraseLocal := false) (simpTheorems := getVCGenTheorems)
  let stats ← dischargeWrapper.with fun discharge? =>
    simpLocation ctx simprocs discharge? (expandOptLocation stx[5])
  if tactic.simp.trace.get (← getOptions) then
    traceSimpCall stx stats.usedTheorems
  return stats.diag

end Elab

section Rules

-- attribute [simp ←] LawfulMonad.bind_pure_comp
-- attribute [vc_gen ←] Id.map_eq Id.bind_eq Id.pure_eq -- cyclic... Just use `Idd`
attribute [vc_gen] map_pure pure_bind bind_assoc bind_pure bind_pure_comp

end Rules

end VCGen
