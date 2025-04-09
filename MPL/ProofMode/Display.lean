import MPL.ProofMode.SGoal

namespace MPL.ProofMode

-- syntax sgoalσ := term ".."?
-- syntax sgoalσs := ("∀ " sgoalσ+)?
syntax sgoalHyp := ident " : " term

syntax sgoalStx := /-ppDedent(ppLine sgoalσs)-/ ppDedent(ppLine sgoalHyp)* ppDedent(ppLine "⊢ₛ " term)

open Lean Expr Meta PrettyPrinter Delaborator SubExpr

@[delab mdata.sgoal]
partial def delabSGoal : Delab := do
  let expr ← instantiateMVars <| ← getExpr

  -- extract environment
  let some goal := parseSGoal? expr | failure

  -- delaborate
  -- let σs ← delabσs goal.σs
  let (_, hyps) ← delabHypotheses goal.hyps ({}, #[])
  let target ← unpackSprop (← delab goal.target)

  -- build syntax
  return ⟨← `(sgoalStx| $hyps.reverse* ⊢ₛ $target:term)⟩
where
  delabHypotheses (hyps : Expr)
      (acc : NameMap Nat × Array (TSyntax ``sgoalHyp)) :
      DelabM (NameMap Nat × Array (TSyntax ``sgoalHyp)) := do
    if let some _ := parseEmptyHyp? hyps then
      return acc
    if let some hyp := parseHyp? hyps then
      let mut (map, lines) := acc
      let (idx, name') :=
        if let some idx := map.find? hyp.name then
          (idx + 1, hyp.name.appendAfter <| if idx == 0 then "✝" else "✝" ++ idx.toSuperscriptString)
        else
          (0, hyp.name)
      let stx ← `(sgoalHyp| $(mkIdent name') : $(← unpackSprop (← delab hyp.p)))
      return (map.insert hyp.name idx, lines.push stx)
    if let some (_, lhs, rhs) := parseAnd? hyps then
      delabHypotheses lhs (← delabHypotheses rhs acc)
    else
      failure
/-
  delabσs (σs : Expr) : DelabM (TSyntax ``sgoalσs) := do
    if σs.isAppOf ``List.nil then
      return ← `(sgoalσs|)
    let mut σs := σs
    let mut stx : Array (TSyntax ``sgoalσ) := #[]
    repeat do
      if let some (_, σ, σs') := σs.app3? ``List.cons then
        stx := stx.push (← `(sgoalσ| $(⟨← delab σ⟩)))
        σs := σs'
        continue
      else if σs.isAppOf ``List.nil then
        break
      else
        stx := stx.push (← `(sgoalσ| $(⟨← delab σs⟩)..))
        break
    `(sgoalσs| ∀ $stx*)
-/

-- @[delab app.Iris.ProofMode.HypMarker]
-- def delabHypMarker : Delab := do unpackIprop (← withAppArg delab)
