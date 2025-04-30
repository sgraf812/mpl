/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
import Lean
import MPL.Idd
import MPL.PredTrans
import MPL.WPSimp

/-!
# Weakest precondition interpretation

This module defines the weakest precondition interpretation `WP` of monadic programs
in terms of predicate transformers `PredTrans`.

This interpretation forms the basis of our notion of Hoare triples.
It is the main mechanism of this library for reasoning about monadic programs.

An instance `WP m ps` determines an interpretation `wp⟦x⟧` of a program `x : m α` in terms of a
predicate transformer `PredTrans ps α`; The monad `m` determines `ps : PostShape` and hence
the particular shape of the predicate transformer.

This library comes with pre-defined instances for common monads and transformers such as

* `WP Id .pure`, interpreting pure computations `x : Id α` in terms of a function (isomorphic to)
  `(α → Prop) → Prop`.
* `WP (StateT σ m) (.arg σ ps)` given an instance `WP m ps`, interpreting `StateM σ α` in terms of
  a function `(α → σ → Prop) → σ → Prop`.
* `WP (ExceptT ε m) (.except ε ps)` given an instance `WP m ps`, interpreting `Except ε α` in terms
  of `(α → Prop) → (ε → Prop) → Prop`.
* `WP (EStateM ε σ) (.except ε (.arg σ .pure))` interprets `EStateM ε σ α` in terms of
  a function `(α → σ → Prop) → (ε → σ → Prop) → σ → Prop`.

These instances are all monad morphisms, a fact which is properly encoded and exploited
by the subclass `WPMonad`.
-/

namespace MPL

/--
  A weakest precondition interpretation of a monadic program `x : m α` in terms of a
  predicate transformer `PredTrans ps α`.
  The monad `m` determines `ps : PostShape`. See the module comment for more details.
-/
class WP (m : Type → Type u) (ps : outParam PostShape) where
  wp {α} (x : m α) : PredTrans ps α

export WP (wp)

open Lean.Parser.Term in
syntax:max "wp⟦" term:min optType "⟧" : term
macro_rules
  | `(wp⟦$x:term⟧) => `(WP.wp $x)
  | `(wp⟦$x:term : $ty⟧) => `(WP.wp ($x : $ty))

open Lean.PrettyPrinter in
@[app_unexpander WP.wp]
protected def unexpandWP : Unexpander
  | `($_ $e) => match e with
    | `(($x : $ty)) => `(wp⟦$x : $ty⟧)
    | _ => `(wp⟦$e⟧)
  | _ => (throw () : UnexpandM _)

section Instances

variable {m : Type → Type u}

instance Id.instWP : WP Id .pure where
  wp x := PredTrans.pure x.run

theorem Id.by_wp {α} {x : α} {prog : Id α} (h : x = Id.run prog) (P : α → Prop) :
  (⌜True⌝ ⊢ₛ (wp prog).apply (PostCond.total P)) → P x := h ▸ (fun h => h True.intro)

instance Idd.instWP : WP Idd .pure where
  wp x := PredTrans.pure x.run

theorem Idd.by_wp {α} {x : α} {prog : Idd α} (h : Idd.run prog = x) (P : α → Prop) :
  (wp prog).apply (PostCond.total P) → P x := h ▸ id

instance StateT.instWP [WP m ps] : WP (StateT σ m) (.arg σ ps) where
  wp x := PredTrans.pushArg (fun s => wp⟦x s⟧)

instance ReaderT.instWP [WP m ps] : WP (ReaderT ρ m) (.arg ρ ps) where
  wp x := PredTrans.pushArg (fun s => (·, s) <$> wp⟦x s⟧)

instance ExceptT.instWP [WP m ps] : WP (ExceptT ε m) (.except ε ps) where
  wp x := PredTrans.pushExcept wp⟦x⟧

instance EStateM.instWP : WP (EStateM ε σ) (.except ε (.arg σ .pure)) where
  wp x := -- Could define as PredTrans.mkExcept (PredTrans.modifyGetM (fun s => pure (EStateM.Result.toExceptState (x s))))
    { apply := fun Q s => match x s with
        | .ok a s' => Q.1 a s'
        | .error e s' => Q.2.1 e s'
      conjunctive := by
        intro _ _
        apply SPred.bientails.of_eq
        ext s
        dsimp
        cases (x s) <;> simp
    }

instance State.instWP : WP (StateM σ) (.arg σ .pure) :=
  inferInstanceAs (WP (StateT σ Id) (.arg σ .pure))
instance Reader.instWP : WP (ReaderM ρ) (.arg ρ .pure) :=
  inferInstanceAs (WP (ReaderT ρ Id) (.arg ρ .pure))
instance Except.instWP : WP (Except ε) (.except ε .pure) :=
  inferInstanceAs (WP (ExceptT ε Id) (.except ε .pure))

theorem StateM.by_wp {α} {x : α × σ} {prog : StateM σ α} (h : StateT.run prog s = x) (P : α × σ → Prop) :
  (wp⟦prog⟧.apply (PostCond.total (fun a s' => P (a, s'))) s) → P x := by
    intro hspec
    simp [wp, PredTrans.pure] at hspec
    exact h ▸ hspec

theorem EStateM.by_wp {α} {x : EStateM.Result ε σ α} {prog : EStateM ε σ α} (h : EStateM.run prog s = x) (P : EStateM.Result ε σ α → Prop) :
  ((wp prog).apply (PostCond.total (fun a s' => P (EStateM.Result.ok a s'))) s) → P x := by
    intro hspec
    simp [wp, PredTrans.pure] at hspec
    split at hspec
    case h_1 a s' heq => rw[← heq] at hspec; exact h ▸ hspec
    case h_2 => contradiction

theorem WP.ReaderT_run_apply [WP m ps] (x : ReaderT ρ m α) :
  wp⟦x.run r⟧.apply Q = wp⟦x⟧.apply (fun a _ => Q.1 a, Q.2) r := rfl

theorem WP.StateT_run_apply [WP m ps] (x : StateT σ m α) :
  wp⟦x.run s⟧.apply Q = wp⟦x⟧.apply (fun a s => Q.1 (a, s), Q.2) s := rfl

theorem WP.ExceptT_run_apply [WP m ps] (x : ExceptT ε m α) :
  wp⟦x.run⟧.apply Q = wp⟦x⟧.apply (fun a => Q.1 (.ok a), fun e => Q.1 (.error e), Q.2) := by
    simp [wp, ExceptT.run]
    congr
    (ext x; cases x) <;> rfl

theorem WP.dite_apply {ps} {Q : PostCond α ps} (c : Prop) [Decidable c] [WP m ps] (t : c → m α) (e : ¬ c → m α) :
  wp⟦if h : c then t h else e h⟧.apply Q = if h : c then wp⟦t h⟧.apply Q else wp⟦e h⟧.apply Q := by split <;> rfl

theorem WP.ite_apply {ps} {Q : PostCond α ps} (c : Prop) [Decidable c] [WP m ps] (t : m α) (e : m α) :
  wp⟦if c then t else e⟧.apply Q = if c then wp⟦t⟧.apply Q else wp⟦e⟧.apply Q := by split <;> rfl

end Instances

open Lean Elab Meta Term Command

theorem congr_apply_Q {α : Type} {m : Type → Type u} (a b : m α) (h : a = b) {ps : PostShape} [WP m ps] (Q : PostCond α ps) :
  wp⟦a⟧.apply Q = wp⟦b⟧.apply Q := by congr

-- the following function is vendored from Mathlib for now.  TODO: Specialize, simplify
/-- If `e` is a projection of the structure constructor, reduce the projection.
Otherwise returns `none`. If this function detects that expression is ill-typed, throws an error.
For example, given `Prod.fst (x, y)`, returns `some x`. -/
private def _root_.Lean.Expr.reduceProjStruct? (e : Expr) : MetaM (Option Expr) := do
  let .const cname _ := e.getAppFn | return none
  let some pinfo ← getProjectionFnInfo? cname | return none
  let args := e.getAppArgs
  if ha : args.size = pinfo.numParams + 1 then
    -- The last argument of a projection is the structure.
    let sarg := args[pinfo.numParams]'(ha ▸ pinfo.numParams.lt_succ_self)
    -- Check that the structure is a constructor expression.
    unless sarg.getAppFn.isConstOf pinfo.ctorName do
      return none
    let sfields := sarg.getAppArgs
    -- The ith projection extracts the ith field of the constructor
    let sidx := pinfo.numParams + pinfo.i
    if hs : sidx < sfields.size then
      return some (sfields[sidx]'hs)
    else
      throwError m!"ill-formed expression, {cname} is the {pinfo.i + 1}-th projection function \
        but {sarg} does not have enough arguments"
  else
    return none

def deriveWPSimpFromEq (eq type : Expr) (baseName : Name) (fieldProjs : List Name := []) : TermElabM Name := do
  let lemmaName := baseName ++ `wp_apply
  let res ← forallTelescopeReducing type fun xs _ => do
    let eq := eq.beta xs
    let_expr Eq ty lhs rhs := (← inferType eq) | throwError "not an equality {eq}"
    -- For eta-reduced equalities such as liftM.eq_def, we have
    --   lhs=liftM, rhs=monadLift, ty=(... → ...).
    -- Need to apply congr lemmas until we see ty=(m α).
    forallTelescopeReducing ty fun ys ty => do
    let mut ty := ty
    let mut eq ← ys.foldlM (fun eq y => mkCongrFun eq y) eq
    let mut lhs := lhs.beta ys
    let mut rhs := rhs.beta ys
    logInfo m!"{xs} {ys} {eq} {ty} {lhs} = {rhs}"
    -- Now for instance equalities such as instMonadReaderOfOfMonadLift.eq_def, we have
    -- For eta-reduced equalities such as liftM.eq_def, we have
    --   lhs=instMonadReaderOfOfMonadLift, rhs={ read := liftM read }
    -- In this case, we expect to have fieldProjs=[read], and this list is pre-filtered
    -- to only contain field names that look like monadic operations.
    -- Apply another congr lemma.
    for fieldProj in fieldProjs do
      let args := ty.getAppArgs
      let us := ty.getAppFn.constLevels!
      let proj := mkApp (mkAppN (mkConst fieldProj us) args)
      eq ← mkCongrArg (mkLambda `x .default ty (proj (.bvar 0))) eq
      lhs := proj lhs
      let .some rhs' ← (proj rhs).reduceProjStruct? | throwError "not a projection {proj rhs}"
      rhs := rhs'
      ty ← inferType lhs
    logInfo m!"{xs} {ys} {eq} {ty} {lhs} = {rhs}"
    let .app m a := ty | throwError m!"not a type application {ty}"
    let (.succ l) ← getLevel ty | throwError m!"not a type {ty}"
    let res := mkAppN (mkConst ``congr_apply_Q [l]) #[a, m, lhs, rhs, eq]
    return (← mkLambdaFVars (xs ++ ys) res)
  check res
  -- Term.synthesizeSyntheticMVarsNoPostponing
  let res ← Term.levelMVarToParam res
  let res ← instantiateMVars res
  let lvls ← Term.getLevelNames
  addDecl <| .thmDecl {
    name := lemmaName,
    levelParams := lvls,
    type := ← inferType res,
    value := res,
  }
  return lemmaName

/-- If the given type returns a structure, return the corresponding structure info.
Example: Given `∀ α, α → Prod α β`, return the structure info for `Prod`. -/
def isConstructorType? [Monad m] [MonadEnv m] (ty : Expr) : m (Option StructureInfo) := do
  return getStructureInfo? (← getEnv) ty.getForallBody.getAppFn.constName

def looksTypeLikeMonadicOp? (ty : Expr) : Bool := ty.getForallBody.isApp

/--
  The command `derive_wp_simp foo` will derive a `wp_simp` lemma that unfolds the definition of `foo`.
  Similarly, `derive_wp_simp instMonadReaderOfMonadLift` will derive a `wp_simp` lemma for `bar` assuming that `foo` is a
  each method in the `instMonadReaderOfMonadLift` instance.
-/
-- TODO: Should be an attribute `wp_simps`
elab "derive_wp_simp " names:ident,+ : command =>
  for name in names.getElems do
    let defn ← getConstInfo name.getId
    liftTermElabM do
      let lvls ← mkFreshLevelMVarsFor defn
      let type ← instantiateTypeLevelParams defn lvls
      if (← isProp type) then
        let thm ← deriveWPSimpFromEq (mkConst name.getId lvls) type name.getId
        liftCommandElabM <| elabCommand (← `(attribute [wp_simp] $(mkIdent thm)))
        return
      if not defn.hasValue then throwError s!"{name} does not have a definition"
      let .some eqn ← getUnfoldEqnFor? (nonRec := true) name.getId | throwError s!"{name} does not have an unfolding theorem"
      let eq ← mkConstWithFreshMVarLevels eqn
      if let .some info ← isConstructorType? defn.type then
        let _structName := info.structName
        -- logInfo _structName
        for fieldInfo in info.fieldInfo do
          let info ← getConstInfo fieldInfo.projFn
          if looksTypeLikeMonadicOp? info.type then
            let thm ← deriveWPSimpFromEq eq (← inferType eq) name.getId [fieldInfo.projFn]
            liftCommandElabM <| elabCommand (← `(attribute [wp_simp] $(mkIdent thm)))
        return
      if looksTypeLikeMonadicOp? defn.type then
        let thm ← deriveWPSimpFromEq eq (← inferType eq) name.getId
        liftCommandElabM <| elabCommand (← `(attribute [wp_simp] $(mkIdent thm)))
        return
      throwError s!"Could not generate wp_simps for {name}"

-- derive_wp_simp readThe, liftM
-- derive_wp_simp instMonadReaderOfOfMonadLift
