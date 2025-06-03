/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
import Lean
import MPL.WPMonad
import MPL.Triple
import MPL.Specs
import MPL.SPred.ProofMode
import MPL.Experimental.Crush
import MPL.Tactics.VCGen

namespace MPL

open Lean Parser Meta Elab Term Command

def forInWithInvariant_list {m : Type → Type u₂} {α : Type} {β : Type} [Monad m]
  (xs : List α) (init : β) (f : α → β → m (ForInStep β)) {ps : PostShape} [WP m ps] (_inv : PostCond (β × List.Zipper xs) ps) : m β :=
    pure () >>= fun _ => forIn xs init f

def forInWithInvariant_range {m : Type → Type u₂} {β : Type} [Monad m]
  (xs : Std.Range) (init : β) (f : Nat → β → m (ForInStep β)) {ps : PostShape} [WP m ps] (_inv : PostCond (β × List.Zipper xs.toList) ps) : m β :=
    pure () >>= fun _ => forIn xs init f

@[spec]
theorem Specs.forInWithInvariant_list {α : Type} {β : Type} ⦃m : Type → Type v⦄ {ps : PostShape}
  [Monad m] [WPMonad m ps]
  {xs : List α} {init : β} {f : α → β → m (ForInStep β)}
  {inv : PostCond (β × List.Zipper xs) ps}
  (step : ∀ b rpref x suff (h : xs = rpref.reverse ++ x :: suff),
      ⦃inv.1 (b, ⟨rpref, x::suff, by simp [h]⟩)⦄
      f x b
      ⦃(fun r => match r with
                 | .yield b' => inv.1 (b', ⟨x::rpref, suff, by simp [h]⟩)
                 | .done b' => inv.1 (b', ⟨xs.reverse, [], by simp⟩), inv.2)⦄) :
  ⦃inv.1 (init, ⟨[], xs, by simp⟩)⦄ forInWithInvariant_list xs init f inv ⦃(fun b => inv.1 (b, ⟨xs.reverse, [], by simp⟩), inv.2)⦄ := by
  simp only [MPL.forInWithInvariant_list, pure_bind]
  exact Specs.forIn_list inv step

@[spec]
theorem Specs.forInWithInvariant_range {β : Type} ⦃m : Type → Type v⦄ {ps : PostShape}
  [Monad m] [WPMonad m ps]
  {xs : Std.Range} {init : β} {f : Nat → β → m (ForInStep β)}
  {inv : PostCond (β × List.Zipper xs.toList) ps}
  (step : ∀ b rpref x suff (h : xs.toList = rpref.reverse ++ x :: suff),
      ⦃inv.1 (b, ⟨rpref, x::suff, by simp [h]⟩)⦄
      f x b
      ⦃(fun r => match r with
                 | .yield b' => inv.1 (b', ⟨x::rpref, suff, by simp [h]⟩)
                 | .done b' => inv.1 (b', ⟨xs.toList.reverse, [], by simp⟩), inv.2)⦄) :
  ⦃inv.1 (init, ⟨[], xs.toList, by simp⟩)⦄ forInWithInvariant_range xs init f inv ⦃(fun b => inv.1 (b, ⟨xs.toList.reverse, [], by simp⟩), inv.2)⦄ := by
  simp only [MPL.forInWithInvariant_range, pure_bind]
  exact Specs.forIn_range inv step

-- Q: Why not also steal the following doElem in the syntax?
-- A: What would we expand `assert ... x` to?
--    It appears we would have to expand x ourselves.
syntax "assert " withPosition(basicFun) ("by " withPosition(Tactic.tacticSeqIndentGt))? : doElem
syntax "assert " withPosition(" => " term) ("by " withPosition(Tactic.tacticSeqIndentGt))? : doElem
syntax "invariant " withPosition(basicFun) ("by " withPosition(Tactic.tacticSeqIndentGt))? : doElem
-- Reasons for why assert and invariant should ultimately be elaborated as part of do-notation:
-- 1. It would be far simpler to elaborate `invariant` with the correct binding of let-mut vars.
-- 2. We could attach the syntax of `by ?prf` blocks as metadata to the elaborated construct (something like `forInWithInvariant`, resp. `assertGadget`).
--    This metadata could then be elaborated by the `xapp` tactic or a specialized simproc for proving `wp⟦forInWithInvariant⟧ Q` and `wp⟦assertGadget⟧ Q`.
--    Presently I do not know how to achieve this with a simple `invariant` macro.
-- 3. We could then elaborate `invariant` together with the `doElem` that follows (or precedes).
--    (Currently, we can only expand to another `doElem`, but not elab to an `Expr` and a `doElem`.)
--    One benefit is that we get better type inference for the Zipper parameter, the `xs : List α` index of which is currently inferred separately to the call to `forIn`.
--    (I don't think that the fact that `xs` is completely decoupled from the actual call to `forIn` loses expressivity, since the user can simply write `xs = xs' ∧ ...` in the invariant.)

def ForIn.toList [ForIn Id ρ α] (xs : ρ) : List α := Id.run do
  let mut acc : List α → List α := id
  for x in xs do
    acc := acc ∘ (x :: ·)
  return acc []

class LawfulForIn (m : Type → Type u) (ρ : Type u) (α : Type u) [Monad m] [ForIn m ρ α] [ForIn Id ρ α] where
  forIn_forIn_toList (xs : ρ) b (f : α → β → m (ForInStep β)) : forIn xs b f = forIn (ForIn.toList xs) b f

@[spec]
def requiresGadget {α : Type} {m : Type → Type u} {ps : PostShape} [WP m ps] (_p : Assertion ps) (x : m α) : m α :=
  x

@[spec]
def ensuresGadget {α : Type} {m : Type → Type u} {ps : PostShape} [WP m ps] (_p : α → Assertion ps) (x : m α): m α :=
  x

@[spec]
def assertGadget {m : Type → Type u} {ps : PostShape} [Monad m] [WP m ps] (_p : Assertion ps) : m Unit :=
  pure ()

-- This one will have the let mut vars as free occurrences
def invariantGadget1.{u} {m : Type → Type u} {ps : PostShape} [Monad m] [WP m ps] (_inv : {α : Type} → {xs:List α} → List.Zipper xs → Assertion ps) : m Unit :=
  pure ()

-- This one will have the let mut vars as bound occurrences in β
def invariantGadget2.{u,v} {β : Type v} {m : Type → Type u} {ps : PostShape} [Monad m] [WP m ps] (_inv : β → {α : Type} → {xs:List α} → List.Zipper xs → Assertion ps) : m Unit :=
  pure ()

@[spec]
theorem Specs.invariantGadget_list {m : Type → Type u₂} {ps : PostShape} {α : Type} {β γ : Type} [Monad m] [WPMonad m ps]
  (xs : List α) (init : β) (f : α → β → m (ForInStep β)) (inv : β → {α : Type} → {xs : List α} → List.Zipper xs → Assertion ps) (k : β → m γ) (Q : PostCond γ ps):
  ⦃wp⟦(do let r ← MPL.forInWithInvariant_list xs init f (PostCond.total fun p => (inv p.1 p.2)); k r)⟧ Q⦄
  (do (invariantGadget2 inv : m Unit); let r ← forIn xs init f; k r)
  ⦃Q⦄ := by
    unfold invariantGadget2 MPL.forInWithInvariant_list
    simp only [pure_bind]
    exact .rfl

@[spec 0]
theorem Specs.invariantGadget_range {m : Type → Type u₂} {ps : PostShape} {β γ : Type} [Monad m] [WPMonad m ps]
  (xs : Std.Range) (init : β) (f : Nat → β → m (ForInStep β)) (inv : β → {α : Type} → {xs : List α} → List.Zipper xs → Assertion ps) (k : β → m γ) (Q : PostCond γ ps):
  ⦃wp⟦(do let r ← MPL.forInWithInvariant_range xs init f (PostCond.total fun p => (inv p.1 p.2)); k r)⟧ Q⦄
  (do (invariantGadget2 inv : m Unit); let r ← forIn xs init f; k r)
  ⦃Q⦄ := by
    unfold invariantGadget2 MPL.forInWithInvariant_range
    simp only [pure_bind]
    exact .rfl

macro_rules
  | `(doElem| assert $xs* => $p) => `(doElem| assertGadget (fun $xs* => $p))
  | `(doElem| assert => $p) => `(doElem| assertGadget $p)
  | `(doElem| invariant $xs* => $p) => `(doElem| invariantGadget1 (fun $xs* => $p))

-- syntax (name := spec)
--   ("requires " withPosition(basicFun))?
--   "ensures " withPosition(basicFun)
--   ("signals " withPosition(basicFun))* :
-- --  optSemicolon("specification_by " Tactic.tacticSeqIndentGt)?) : term

def spec : Parser := leading_parser
  optional ("forall " >> withPosition (many1 (ppSpace >> (Term.binderIdent <|> bracketedBinder))))
  >> optional ("requires " >> (withPosition basicFun <|> " => " >> termParser))
  >> "ensures " >> withPosition basicFun
  >> many ("signals " >> withPosition basicFun)
--def optSpec : Parser := Lean.Parser.optional spec

/-- Skip input until the next character that satisfies the predicate, then skip whitespace -/
private def skipUntil (pred : Char → Bool) : Parser where
  fn :=
    andthenFn
      (takeUntilFn pred)
      (takeWhileFn Char.isWhitespace)

/-- Skip input until the next whitespace character (used for error recovery for certain tokens) -/
private def skipUntilWs : Parser := skipUntil Char.isWhitespace

/-- Skip input until the next whitespace character or delimiter (used for error recovery for certain
    tokens, especially names that occur in signatures) -/
private def skipUntilWsOrDelim : Parser := skipUntil fun c =>
  c.isWhitespace || c == '(' || c == ')' || c == ':' || c == '{' || c == '}' || c == '|'

def newdefinition     := leading_parser
  -- "def " >> recover declId skipUntilWsOrDelim >> ppIndent optDeclSig >> declVal >> optDefDeriving
  "def " >> recover declId skipUntilWsOrDelim >> ppIndent optDeclSig >> ppIndent spec >> declVal >> optDefDeriving

@[command_parser]
def newdeclaration := leading_parser
  declModifiers false >> newdefinition

--def newdeclaration.blah : TSyntax ``declVal → CommandElabM (TSyntax ``declVal)
--  | `(newdeclVal| := $bdy:declBody $x $wheres $deriv:optDefDeriving) => do
--def newdeclaration.toOldDeclaration : TSyntax ``newdeclaration → CommandElabM (TSyntax ``declaration)
--  | `(newdeclaration| $mods:declModifiers $defn:newdefinition) => match defn with
--    | `(newdefinition| def $id $sig $spc:spec := $bdy:declBody $x $wheres $specby $deriv:optDefDeriving) => do
--    | _ => throwUnsupportedSyntax
--  | _ => throwUnsupportedSyntax

def patch_invariant (e : Expr) (args : Array Expr := Array.empty) (names : Array Name := Array.empty) : TermElabM Expr := match e with
-- we collect patched args and match against those args in the const case:
| .app f x => do let x ← patch_invariant x #[] names; patch_invariant f (args.push x) names
| .const n ls =>  match n, args.size with
  | ``Bind.bind, 6 => match_expr args[1]! with
    | invariantGadget1 m ps monad wp inv => do
      let u := args[1]!.getAppFn.constLevels!.head!
--      dbg_trace "go"
      let mut bvshift := 0
      let mut body := args[0]!
      while true do
        if let .letE _ _ _ b _ := body then
          body := b
          bvshift := bvshift + 1
        else break
      let .lam _ _ b _ := body | throwError "bfoo";
      body := b
      bvshift := bvshift + 1
      while true do
        if let some init := (match_expr body with | ForIn.forIn _ _ _ _ _ _ _ init _ => some init | _ => none) then
          -- init contains the good stuff; a tuple of all the mut vars
          body := init
          break
        else if let .letE _ _ _ b _ := body then
          body := b
          bvshift := bvshift + 1
          continue
        else if let some x := (match_expr body with | Bind.bind _ _ _ _ x _ => some x | _ => none) then
          body := x
          continue
        else throwError "bfoo"
      let mut prod := body
      let prod_ty0 ← inferType prod -- This inferType is currently the only reason we need TermElabM. We can likely reconstruct the type from the match on MProd.mk below to make it pure...
      let .succ v ← getLevel prod_ty0 | throwError "Cannot happen; Prop-sorted MProd"
--      dbg_trace prod_ty0
      let mut prod_ty := prod_ty0
      let mut mut_vars := Array.empty
      while true do
        let_expr MProd.mk _ _ b xs := prod | break
        let .bvar b := b | throwError "bfoo"
        mut_vars := mut_vars.push (b - bvshift)
        prod := xs
      let .bvar b := prod | throwError "bfoo"
      mut_vars := mut_vars.push (b - bvshift)
--      dbg_trace mut_vars
--      dbg_trace inv
      let mut wrapper := fun e => mkLambda `x .default prod_ty e
      for bvarId in mut_vars do
        let name := names[names.size - bvarId - 1]!
        if let some (bvar_ty, prod_ty') := match_expr prod_ty with | MProd bvar_ty prod_ty' => some (bvar_ty, prod_ty') | _ => none then
          wrapper := fun e =>
            wrapper <|
            mkLet name bvar_ty (.proj ``MProd 0 (.bvar 0)) <|
            mkLet `x prod_ty' (.proj ``MProd 1 (.bvar 1)) <|
            e
          prod_ty := prod_ty'
        else
          wrapper := fun e =>
            wrapper <|
            mkLet name prod_ty (.bvar 0) <|
            e
      let some max := mut_vars.foldr (fun a mb => max (some a) mb) none | throwError "TODO: handle invariants without mut vars"
      let mut subst : Array Expr := mkArray (max + 1) (.bvar 0)
      for i in [0:subst.size] do
        subst := subst.set! i (.bvar (i + mut_vars.size * 2))
      -- up until now, subst is the identity substitution for the body of wrapper (which shifts by mut_vars.size * 2)
      for i in [0:mut_vars.size] do
        subst := subst.set! mut_vars[i]! (.bvar ((mut_vars.size - i - 1) * 2))
--      dbg_trace subst
      let inv := inv.instantiate subst
      let inv := wrapper inv
--      dbg_trace inv
--      logInfo inv
--      logInfo (mkAppRev (Expr.const n ls) (args.set! 1 (mkApp6 (mkConst ``invariantGadget2 [u,v]) prod_ty0 m ps monad wp inv)))
      pure (mkAppRev (Expr.const n ls) (args.set! 1 (mkApp6 (mkConst ``invariantGadget2 [u,v]) prod_ty0 m ps monad wp inv)))
    | _ => pure (mkAppRev (Expr.const n ls) args)
  | _, _ => pure (mkAppRev (Expr.const n ls) args)
-- the congruent cases:
| .proj i n x => do return mkAppRev (.proj i n (← patch_invariant x #[] names)) args
| .mdata d x => do return .mdata d (← patch_invariant x args names) -- NB: .mdata does not obstruct applicative contexts
-- | .mdata d x => do return mkAppRev (.mdata d (← patch_invariant x #[] names)) args
| .sort u => do return mkAppRev (.sort u) args
| .lit l => do return mkAppRev (.lit l) args
| .mvar mvarId => do return mkAppRev (.mvar mvarId) args
| .fvar fvarId => do return mkAppRev (.fvar fvarId) args
| .bvar bvarId => do return mkAppRev (.bvar bvarId) args
-- the binder cases:
| .lam x ty body bi => do return mkAppRev (.lam x ty (← patch_invariant body #[] (names.push x)) bi) args
| .letE x ty val body b => do return mkAppRev (.letE x ty (← patch_invariant val #[] names) (← patch_invariant body #[] (names.push x)) b) args -- TODO: let could be an applicative context
| .forallE x ty body bi => do return mkAppRev (.forallE x ty (← patch_invariant body #[] (names.push x)) bi) args


@[command_elab newdeclaration]
partial def elab_newdecl : CommandElab := fun decl => do
  -- newdeclaration := declModifiers false >> newdefinition
  -- newdefinition := "def " >> recover declId skipUntilWsOrDelim >> ppIndent optDeclSig >> ppIndent spec >> declVal >> optDefDeriving
  let defn     := decl[1]
  let declKind := defn.getKind
  let declId := defn[1][0].getId
  let some stxinfo := decl.getInfo? | throwUnsupportedSyntax
  let some declinfo := defn.getInfo? | throwUnsupportedSyntax
--  dbg_trace defn
--  dbg_trace decl
--  dbg_trace decl.getNumArgs
  -- Step 1: Massage the syntax into a refined helper definition that
  --   * the def elaborator accepts, and that
  --   * elaborates requires, ensures, signals, assert and invariants for us.
  let spec := defn[3]
  let foralls? := if spec[0].isMissing then none else some spec[0][1].getArgs
  let refinedDecl1 := defn[1].setArg 0 <| match defn[1][0] with
    | .ident info ss val _ => Syntax.ident info ss (val ++ Name.mkSimple "refined1") []
    | _ => panic "die" -- TODO
  -- dbg_trace defn[2][0]
  let optDeclSig := match defn[2].isMissing, foralls? with
    | _,  none => defn[2]
    | false, some bndrs => defn[2].setArg 0 (defn[2][0].setArgs (defn[2][0].getArgs ++ bndrs))
    | true, some bndrs => panic "die also"  -- TODO
  let numProgBinders : Nat := if defn[2].isMissing then 65536 else defn[2][0].getNumArgs
  let olddeclValRefined ← match defn[4] with
    | .node info ``declValSimple args => do
      let req := spec[1] -- might be missing. we check below.
      let ens : TSyntax ``basicFun := ⟨spec[3]⟩
      -- defn[4][1] is the term/do block; we'll patch it with the gadgets for requires and ensures
      let body ←
        if req[1].isMissing
        then `(requiresGadget ⌜True⌝ (ensuresGadget (by exact (fun $ens:basicFun)) $(⟨defn[4][1]⟩)))
        else if req[1].getKind = ``basicFun
        then `(requiresGadget (fun $(⟨req[1]⟩):basicFun) (ensuresGadget (by exact (fun $ens:basicFun)) $(⟨defn[4][1]⟩)))
        else `(requiresGadget ($(⟨req[2]⟩):term) (ensuresGadget (by exact (fun $ens:basicFun)) $(⟨defn[4][1]⟩)))
      pure (Syntax.node info ``declValSimple (Array.set! args 1 body))
    | _ => throwUnsupportedSyntax
  -- dbg_trace olddeclValRefined
  let olddefn := Syntax.node5 stxinfo ``Parser.Command.definition defn[0] refinedDecl1 optDeclSig olddeclValRefined defn[5]
  let olddecl := Syntax.node2 declinfo ``Parser.Command.declaration decl[0] olddefn
--  dbg_trace olddecl
  elabDeclaration olddecl
  let ns ← getCurrNamespace
  let declId := ns ++ declId
  let refinedDeclId1 := declId ++ Name.mkSimple "refined1"
  let refinedDeclId2 := declId ++ Name.mkSimple "refined2"
  let .some (.defnInfo defn) := (← getEnv).find? refinedDeclId1 | throwUnsupportedSyntax
--  log defn.name
--  dbg_trace defn.value
--  log defn.name
  -- Step 2: Rewrite invariantGadget1 to invariantGadget2, thus closing over the let mut vars
--  log defn.value
  runTermElabM fun _ => do
    let newval ← patch_invariant defn.value
--    synthesizeSyntheticMVarsNoPostponing
--    let newval ← instantiateMVars newval
--    log newval
    addDecl (.defnDecl { defn with
      name := refinedDeclId2
      value := newval
    })
  let .some (.defnInfo defn) := (← getEnv).find? refinedDeclId2 | throwUnsupportedSyntax
--  dbg_trace defn.name
--  dbg_trace defn.value

  runTermElabM fun vars => do
  let rec spec_ty (call : Expr) (body : Expr) (progBinders : Nat) : (ty : Expr) → TermElabM (Expr × Expr)
    | .forallE x ty body_ty info => withLocalDecl x info ty fun a => do
      -- dbg_trace x
      -- dbg_trace progBinders
      let (refined_spec, erased_value) ← spec_ty (mkApp call a) (mkApp body a).headBeta (progBinders - 1) (body_ty.instantiate1 a)
      if progBinders = 0 then
        return (← mkForallFVars #[a] refined_spec, erased_value)
      else
        return (← mkForallFVars #[a] refined_spec, ← mkLambdaFVars #[a] erased_value)
    | ty => do
    let mut body := body
--    logInfo body
    let_expr requiresGadget _α _m _ps _WP P body' := body | throwError "no requiresGadget"
    body := body'
    let_expr ensuresGadget α m ps wp Q body' := body | throwError "no ensuresGadget"
    body := body'
    let some u := Level.dec (← getLevel (mkApp m α)) | throwError "invalid level (0?)"
--    dbg_trace u
    let Q := mkApp3 (mkConst ``PostCond.total) α ps Q
    -- dbg_trace P
    -- dbg_trace Q
    -- dbg_trace body
    -- unfold assertGadget and invariantGadget applications
    let pure_unit ← elabTerm (← `(pure ())) (some (mkApp m (mkConst ``Unit)))
    body := body.replace fun e => match_expr e with
      | assertGadget _ _ _ _ _ => some pure_unit
      | invariantGadget2 _ _ _ _ _ _ => some pure_unit
      | _ => none
    -- dbg_trace body
    -- spec := leading_parser
    --  "forall " (Term.binderIdent <|> bracketedBinder)+ ("requires" basicFun)? "ensures" basicFun ("signals" basicFun)*
    -- let `($xs => $e) := spec[0]
    -- dbg_trace spec[2][1]
    -- dbg_trace call
    let refined_triple_ty := mkApp7 (mkConst ``Triple [u]) m ps wp α call P Q
    return (refined_triple_ty, body)
  let (refined_spec, erased_value) ← spec_ty (mkConst defn.name (defn.levelParams.map .param)) defn.value numProgBinders defn.type
  let erased_value ← instantiateMVars erased_value
  let erased_ty ← inferType erased_value
  -- dbg_trace erased_value
  -- dbg_trace erased_ty
  --log erased_value
  addDecl (.defnDecl { defn with
    name := declId
    type := erased_ty
    -- value := ← Term.elabTermEnsuringType (← `(by sorry)) refined_spec
    value := erased_value
  })
  let .some (.defnInfo defn) := (← getEnv).find? declId | throwUnsupportedSyntax
  -- dbg_trace defn.name
  synthesizeSyntheticMVarsNoPostponing
  let refined_spec ← instantiateMVars refined_spec
  let rec erase_spec (erased_call : Expr) (progBinders : Nat) : Expr → TermElabM Expr
    | .forallE x ty refined_spec info => withLocalDecl x info ty fun a => do
--      dbg_trace x
--      dbg_trace progBinders
      let erased_spec ← erase_spec (if progBinders = 0 then erased_call else mkApp erased_call a) (progBinders - 1) (refined_spec.instantiate1 a)
      return (← mkForallFVars #[a] erased_spec)
    | mkApp3 trpl _refined_call P Q => do
      -- dbg_trace _refined_call
      return (mkApp3 trpl erased_call P Q)
    | _ => throwError "no triple"
  --log refined_spec
  let erased_spec ← erase_spec (mkConst defn.name) numProgBinders refined_spec
  -- dbg_trace erased_spec
  let levelParams := collectLevelParams {} erased_spec |>.params
  -- dbg_trace levelParams

--  let refined_spec ← instantiateMVars (← spec_ty (← mkConstWithFreshMVarLevels defn.name) defn.type)
  let val := (← Term.elabTerm (← `(by unfold $(mkIdent refinedDeclId2); intros; mvcgen <;> repeat crush)) (.some refined_spec) (catchExPostpone := false))
  synthesizeSyntheticMVarsNoPostponing
  let erased_spec ← instantiateMVars erased_spec
  let val ← instantiateMVars val
--  dbg_trace refined_spec.hasLevelMVar
--  dbg_trace refined_spec.hasMVar
--  dbg_trace erased_spec.hasLevelMVar
--  dbg_trace erased_spec.hasMVar
--  dbg_trace val.hasLevelMVar
--  dbg_trace val.hasMVar
  addDecl (.thmDecl {
    name := declId ++ Name.mkSimple "spec"
    levelParams := defn.levelParams
    type := erased_spec
    -- value := ← Term.elabTermEnsuringType (← `(by sorry)) refined_spec
    value := val
  })

namespace Test

abbrev fib_spec : Nat → Nat
| 0 => 0
| 1 => 1
| n+2 => fib_spec n + fib_spec (n+1)

set_option trace.mpl.tactics.spec true in
set_option trace.Meta.isDefEq true in
def fib_impl (n : Nat) : Idd Nat
  ensures r => r = fib_spec n
:= do
  if n = 0 then return 0
  let mut a := 0
  let mut b := 1
  invariant xs => a = fib_spec xs.rpref.length ∧ b = fib_spec (xs.rpref.length + 1)
  for _ in [1:n] do
    let a' := a
    a := b
    b := a' + b
  return b

--#check fib_impl.spec

theorem fib_triple : ⦃⌜True⌝⦄ fib_impl n ⦃⇓ r => r = fib_spec n⦄ := by
  unfold fib_impl
  mintro -
  if h : n = 0 then simp [h] else
  simp only [h, reduceIte]
  mspec
  mspec
  mspec Specs.forIn_range ?inv ?step
  case inv => exact PostCond.total fun (⟨a, b⟩, xs) => a = fib_spec xs.rpref.length ∧ b = fib_spec (xs.rpref.length + 1)
  case pre1 => simp_all
  case step => intros; intro _; simp_all
  simp_all [Nat.sub_one_add_one]

theorem fib_correct {n} : (fib_impl n).run = fib_spec n := by
  generalize h : (fib_impl n).run = x
  apply Idd.by_wp h
  apply fib_impl.spec n True.intro

def fib_impl_strange (n : Nat) : Idd Nat
  ensures r => r = fib_spec n
:= do
  if n = 0 then return 0
  let mut a := 0
  let mut b := 1
  let c := 13
  let d := 14
  let mut e := 4
  invariant xs => a = fib_spec xs.rpref.length ∧ b = fib_spec (xs.rpref.length + 1) ∧ c = 13 ∧ d = 14
  for _ in [1:n] do
    let a' := a
    a := b
    b := a' + b
    e := 4
  return b

private abbrev st : SVal ((Nat × Nat)::σs) (Nat × Nat) := fun s => SVal.pure s

def mkFreshInt {m : Type → Type} [Monad m] : StateT (Nat × Nat) m Nat
  forall {ps} [WPMonad m ps] (n o : Nat)
  requires => ⌜(#st).1 = n ∧ (#st).2 = o⌝
  ensures r => ⌜r = n ∧ (#st).1 = n + 1 ∧ (#st).2 = o⌝
:= do
  let n ← Prod.fst <$> get
  -- assert _ => ⌜o = 13⌝
  modify (fun s => (s.1 + 1, s.2))
  pure n

/- signals is not implemented yet
--set_option trace.Elab.definition true in
def blah1 (n: Nat) : StateM Nat Bool
  requires s => s > 4
  ensures r s => r = (n + s % 2 == 0)
  signals _ _ => False
:= do
  if n == 0 then return false
  let tmp := (← get) + n
  assert _ => tmp > n
  let mut x := 0
  invariant xs _s => x = xs.rpref.sum
  for i in [1:tmp] do
    x := x + i
  return (tmp % 2 == 0)
-- specification_by
--   · xwp; sorry
--   · inv x (rpref, y::suff) → inv (x + i) (y::rpref,suff)
--   · Q <return false>
--   · Q <return (tmp % 2 == 0)>


def foo := 1

def ex (n : Nat) : ExceptT Nat (StateT Nat Idd) Nat
  requires s => s = 4 ∧ n = 0
  ensures (r:Nat) (s : Nat) => False
  signals e s => e = 42 ∧ s = 4
:= do
  let mut x := n
  let s ← get
  --invariant s => True
  for i in [1:s] do
    x := x + i
    if x > 4 then throw 42
  set 1
  return x
-/
