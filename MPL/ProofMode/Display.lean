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

/-
-- Can't get this to work yet; doesn't make a difference.
def Delab.addHypInfo (stx : Syntax) (σs : Expr) (hyp : Hyp) : DelabM Unit := do
  let ty := mkApp2 (mkConst ``HypMarker) σs hyp.p
  let lctx := (← getLCtx).mkLocalDecl ⟨hyp.uniq⟩ hyp.name ty
  let fvar := mkFVar ⟨hyp.uniq⟩
  let info := Elab.Info.ofTermInfo {
    elaborator := `Delab,
    stx := stx,
    lctx := lctx,
    expectedType? := ty,
    expr := fvar,
    isBinder := true
  }
  let pos ← getPos
  modify fun s => { s with infos := s.infos.insert pos info }
-/

@[app_delab MGoalEntails]
partial def delabMGoal : Delab := do
  let expr ← instantiateMVars <| ← getExpr

  -- extract environment
  let some goal := parseMGoal? expr | failure

  -- delaborate
  -- let σs ← delabσs goal.σs
  let (_, hyps) ← withAppFn ∘ withAppArg <| delabHypotheses goal.σs ({}, #[])
  let target ← SPred.Notation.unpack (← withAppArg <| delab)

  -- build syntax
  return ⟨← `(mgoalStx| $hyps.reverse* ⊢ₛ $target:term)⟩
where
  delabHypotheses (σs : Expr)
      (acc : NameMap Nat × Array (TSyntax ``mgoalHyp)) :
      DelabM (NameMap Nat × Array (TSyntax ``mgoalHyp)) := do
    let hyps ← getExpr
    if let some _ := parseEmptyHyp? hyps then
      return acc
    if let some hyp := parseHyp? hyps then
      let mut (map, lines) := acc
      let (idx, name') :=
        if let some idx := map.find? hyp.name then
          (idx + 1, hyp.name.appendAfter <| if idx == 0 then "✝" else "✝" ++ idx.toSuperscriptString)
        else
          (0, hyp.name)
      let name' := mkIdent name'
      -- Delab.addHypInfo name' σs hyp -- see comment above
      let stx ← `(mgoalHyp| $name' : $(← SPred.Notation.unpack (← withMDataExpr <| delab)))
      return (map.insert hyp.name idx, lines.push stx)
    if (parseAnd? hyps).isSome then
      let acc_rhs ← withAppArg <| delabHypotheses σs acc
      let acc_lhs ← withAppFn ∘ withAppArg <| delabHypotheses σs acc_rhs
      return acc_lhs
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

@[app_delab HypMarker]
def delabHypMarker : Delab := do SPred.Notation.unpack (← withAppArg delab)
