import MPL.ProofMode.Tactics.Basic
import MPL.ProofMode.Tactics.Intro
import MPL.ProofMode.Tactics.Assumption
import MPL.WP
import MPL.SpecAttr

namespace MPL.ProofMode.Tactics
open Lean Elab Tactic Meta

initialize registerTraceClass `mpl.tactics.spec

@[spec]
theorem _root_.MPL.Specs.pure {m : Type → Type} {ps : PredShape} [Monad m] [WPMonad m ps] {α} {a : α} {Q : PostCond α ps} :
  ⦃Q.1 a⦄ (pure (f:=m) a) ⦃Q⦄ := triple_pure a .rfl

@[spec]
theorem _root_.MPL.Specs.bind {m : Type → Type} {ps : PredShape} [Monad m] [WPMonad m ps] {α β} {x : m α} {f : α → m β} {Q : PostCond β ps} :
  ⦃wp⟦x⟧.apply (fun a => wp⟦f a⟧.apply Q, Q.2)⦄ (x >>= f) ⦃Q⦄ := triple_bind x f .rfl (fun _ => .rfl)

theorem Spec.apply {m : Type → Type} {ps : PredShape} [WP m ps] {α} {x : m α} {P : PreCond ps} {Q Q' : PostCond α ps}
  (h : ⦃P⦄ x ⦃Q⦄) (hpost : SPred.entails (wp⟦x⟧.apply Q) (wp⟦x⟧.apply Q')) :
  P.entails (wp⟦x⟧.apply Q') := SPred.entails.trans h hpost

theorem Spec.apply_mono {m : Type → Type} {ps : PredShape} [WP m ps] {α} {x : m α} {P : PreCond ps} {Q Q' : PostCond α ps}
  (h : ⦃P⦄ x ⦃Q⦄) (hpost : Q.entails Q') :
  P.entails (wp⟦x⟧.apply Q') := Spec.apply h (wp⟦x⟧.mono _ _ hpost)

theorem Spec.entails_total {α} {ps : PredShape} (p : α → PreCond ps) (q : PostCond α ps) :
  (∀ a, p a ⊢ₛ q.1 a) → PostCond.total p ⊢ₚ q := (PostCond.entails_total p q).mpr

theorem Spec.entails_partial {α} {ps : PredShape} (p : PostCond α ps) (q : α → PreCond ps) :
  (∀ a, p.1 a ⊢ₛ q a) → p ⊢ₚ PostCond.partial q := (PostCond.entails_partial p q).mpr

def mFindSpec (stx? : Option (TSyntax `term)) (u : Level) (m : Expr) (ps : Expr) (instWP : Expr) (α : Expr) (prog : Expr) : TacticM (Expr × Expr × Expr) := do
  let stx ← stx?.getDM do
    unless prog.getAppFn'.isConst do throwError s!"not an application of a constant: {prog}"
    let specs ← specAttr.find? prog
    if specs.isEmpty then throwError s!"no specs found for {prog}"
    if specs.size > 1 then throwError s!"multiple specs found for {prog}: {specs}"
    return mkIdent specs[0]!
  trace[mpl.tactics.spec] "spec syntax: {stx}"
  let spec ← elabTermForApply stx
  trace[mpl.tactics.spec] "inferred spec, pre instantiate telescope: {spec}"
  let specTy ← inferType spec
  let (mvs, _bis, specTy) ← forallMetaTelescope specTy -- This could be done more efficiently without MVars
  let spec := spec.beta mvs
  trace[mpl.tactics.spec] "inferred spec, post instantiate telescope: {spec}"
  let_expr triple _m _ps _inst _α _prog P Q := specTy | throwError "spec type not a triple application {specTy}"
  let expectedTy := mkApp7 (mkConst ``triple [u]) m ps instWP α prog P Q
  -- We allow synthetic opaque metavars to be assigned in the following step since the `isDefEq` is not really
  -- part of the elaboration, but part of the tactic.
  unless (← withAssignableSyntheticOpaque <| isDefEq specTy expectedTy) do
    Term.throwTypeMismatchError none expectedTy specTy spec
  trace[mpl.tactics.spec] "inferred spec, post check: {← instantiateMVars spec} : {← instantiateMVars specTy}"
  return (spec, P, Q)

def mkProj' (n : Name) (i : Nat) (Q : Expr) : MetaM Expr := do
  return (← projectCore? Q i).getD (mkProj n i Q)

mutual
partial def dischargePostEntails (α : Expr) (ps : Expr) (Q : Expr) (Q' : Expr) (goalTag : Name) (resultName : Name) (discharge : Expr → Name → MetaM Expr) : MetaM Expr := do
  -- Often, Q' is fully instantiated while Q contains metavariables. Try refl
  if (← isDefEq Q Q') then
    return mkApp3 (mkConst ``PostCond.entails_refl) α ps Q'
  -- Otherwise decompose the conjunction
  let Q ← whnfR Q
  let Q' ← whnfR Q'
  let prf₁ ← withLocalDeclD resultName α fun a => do
    let Q1a := (← mkProj' ``Prod 0 Q).betaRev #[a]
    let Q'1a := (← mkProj' ``Prod 0 Q').betaRev #[a]
    let σs := mkApp (mkConst ``PredShape.args) ps
    let goal := mkApp3 (mkConst ``SPred.entails) σs Q1a Q'1a
    mkLambdaFVars #[a] (← discharge goal (goalTag ++ `success))
  let prf₂ ← dischargeFailEntails ps (← mkProj' ``Prod 1 Q) (← mkProj' ``Prod 1 Q') (goalTag ++ `except) discharge
  mkAppM ``And.intro #[prf₁, prf₂] -- This is just a bit too painful to construct by hand

partial def dischargeFailEntails (ps : Expr) (Q : Expr) (Q' : Expr) (goalTag : Name) (discharge : Expr → Name → MetaM Expr) : MetaM Expr := do
  if ps.isAppOf ``PredShape.pure then
    return mkConst ``True.intro
  if ← isDefEq Q Q' then
    return mkApp2 (mkConst ``FailConds.entails_refl) ps Q
  if ← isDefEq Q (mkConst ``FailConds.false) then
    return mkApp2 (mkConst ``FailConds.entails_false) ps Q'
  if ← isDefEq Q' (mkConst ``FailConds.true) then
    return mkApp2 (mkConst ``FailConds.entails_true) ps Q
  -- the remaining cases are recursive.
  if let some (_σ, ps) := ps.app2? ``PredShape.arg then
    return ← dischargeFailEntails ps Q Q' goalTag discharge
  let some (ε, ps) := ps.app2? ``PredShape.except
    | throwError "Internal error: unknown ps"
  let Q ← whnfR Q
  let Q' ← whnfR Q'
  let prf₁ ← withLocalDeclD goalTag ε fun e => do
    let Q1e := (← mkProj' ``Prod 0 Q).betaRev #[e]
    let Q'1e := (← mkProj' ``Prod 0 Q').betaRev #[e]
    let σs := mkApp (mkConst ``PredShape.args) ps
    let goal := mkApp3 (mkConst ``SPred.entails) σs Q1e Q'1e
    mkLambdaFVars #[e] (← discharge goal (goalTag ++ `handle))
  let prf₂ ← dischargeFailEntails ps (← mkProj' ``Prod 1 Q) (← mkProj' ``Prod 1 Q') (goalTag ++ `except) discharge
  mkAppM ``And.intro #[prf₁, prf₂] -- This is just a bit too painful to construct by hand
end

def dischargeMGoal (goal : MGoal) (goalTag : Name) (discharge : Expr → Name → MetaM Expr) : MetaM Expr := do
  trace[mpl.tactics.spec] "dischargeMGoal: {goal.target}"
  -- simply try one of the assumptions for now. Later on we might want to decompose conjunctions etc; full xsimpl
  let some prf ← goal.assumption | discharge goal.toExpr goalTag
  return prf

def mSpec (goal : MGoal) (spec : Option (TSyntax `term)) (discharge : Expr → Name → MetaM Expr) (resultName := `r) : TacticM Expr := do
  -- Elaborate the spec, apply style
  let T := goal.target.consumeMData -- had the error below trigger in Lean4Lean for some reason
  let_expr PredTrans.apply _ps _α wp Q' := T | throwError "target not a PredTrans.apply application {T}"
  let_expr WP.wp m ps instWP α x := wp | throwError "target not a wp application {wp}"
  let [u] := wp.getAppFn'.constLevels! | throwError "Internal error: wrong number of levels in wp application"
  let (spec, P, Q) ← mFindSpec spec u m ps instWP α x
  -- apply the spec
  let postPrf ← dischargePostEntails α ps Q Q' `post resultName discharge
  let HPPrf ← dischargeMGoal { goal with target := P } `pre discharge
  let PTPrf := mkApp10 (mkConst ``Spec.apply_mono) m ps instWP α x P Q Q' spec postPrf
  return mkApp6 (mkConst ``SPred.entails.trans) goal.σs goal.hyps P goal.target HPPrf PTPrf

private def addMVar (mvars : IO.Ref (List MVarId)) (goal : Expr) (name : Name) : MetaM Expr := do
  let m ← mkFreshExprSyntheticOpaqueMVar goal (tag := name)
  mvars.modify (m.mvarId! :: ·)
  return m

syntax "mspec_no_bind" (ppSpace colGt term)? : tactic

elab "mspec_no_bind" spec:optional(term) : tactic => withMainContext do
  let (mvar, goal) ← mStart (← getMainGoal)
  let goals ← IO.mkRef []
  mvar.assign (← mSpec goal spec (addMVar goals))
  let goals ← goals.get
  if let [mvar'] := goals then mvar'.setTag (← mvar.getTag)
  replaceMainGoal goals

syntax "mspec_no_simp" (ppSpace colGt term)? : tactic

-- or: xspec
syntax "mspec" (ppSpace colGt term)? : tactic
macro_rules
  | `(tactic| mspec_no_simp $[$spec]?) => `(tactic| ((try mspec_no_bind MPL.Specs.bind); mspec_no_bind $[$spec]?))
  | `(tactic| mspec $[$spec]?)         => `(tactic| mspec_no_simp $[$spec]? <;> try simp +contextual only [gt_iff_lt, Prod.mk_le_mk, le_refl, and_true, PostCond.entails, FailConds.entails_false, FailConds.entails_refl, FailConds.entails_true, FailConds.pure_def, SPred.entails.refl])

/-
abbrev M := StateT Nat (StateT Char (StateT Bool (StateT String Idd)))
example : ⦃isValid⦄ pure (f := M) (a + b + c) ⦃⇓r => ⌜r > 100⌝ ∧ isValid⦄ := by
  mintro h
  -- set_option trace.Meta.whnf true in
  set_option trace.mpl true in
  mspec
-/
