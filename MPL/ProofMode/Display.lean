/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Sebastian Graf
-/
import MPL.ProofMode.MGoal

namespace MPL.ProofMode

syntax mgoalHyp := ident " : " term

syntax mgoalStx := /-ppDedent(ppLine mgoalσs)-/ ppDedent(ppLine mgoalHyp)* ppDedent(ppLine "⊢ₛ " term)

open Lean Expr Meta PrettyPrinter Delaborator SubExpr

@[delab mdata.mgoal]
partial def delabMGoal : Delab := do
  let expr ← instantiateMVars <| ← getExpr

  -- extract environment
  let some goal := parseMGoal? expr | failure

  -- delaborate
  -- let σs ← delabσs goal.σs
  let (_, hyps) ← delabHypotheses goal.hyps ({}, #[])
  let target ← SPred.Notation.unpack (← delab goal.target)

  -- build syntax
  return ⟨← `(mgoalStx| $hyps.reverse* ⊢ₛ $target:term)⟩
where
  delabHypotheses (hyps : Expr)
      (acc : NameMap Nat × Array (TSyntax ``mgoalHyp)) :
      DelabM (NameMap Nat × Array (TSyntax ``mgoalHyp)) := do
    if let some _ := parseEmptyHyp? hyps then
      return acc
    if let some hyp := parseHyp? hyps then
      let mut (map, lines) := acc
      let (idx, name') :=
        if let some idx := map.find? hyp.name then
          (idx + 1, hyp.name.appendAfter <| if idx == 0 then "✝" else "✝" ++ idx.toSuperscriptString)
        else
          (0, hyp.name)
      let stx ← `(mgoalHyp| $(mkIdent name') : $(← SPred.Notation.unpack (← delab hyp.p)))
      return (map.insert hyp.name idx, lines.push stx)
    if let some (_, lhs, rhs) := parseAnd? hyps then
      delabHypotheses lhs (← delabHypotheses rhs acc)
    else
      failure
/-
  delabσs (σs : Expr) : DelabM (TSyntax ``mgoalσs) := do
    if σs.isAppOf ``List.nil then
      return ← `(mgoalσs|)
    let mut σs := σs
    let mut stx : Array (TSyntax ``mgoalσ) := #[]
    repeat do
      if let some (_, σ, σs') := σs.app3? ``List.cons then
        stx := stx.push (← `(mgoalσ| $(⟨← delab σ⟩)))
        σs := σs'
        continue
      else if σs.isAppOf ``List.nil then
        break
      else
        stx := stx.push (← `(mgoalσ| $(⟨← delab σs⟩)..))
        break
    `(mgoalσs| ∀ $stx*)
-/

-- @[delab app.Iris.ProofMode.HypMarker]
-- def delabHypMarker : Delab := do unpackIprop (← withAppArg delab)
