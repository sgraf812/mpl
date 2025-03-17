import Lean
import MPL.WPMonad
import MPL.Triple
import MPL.Tactic

namespace MPL

open Lean Parser Meta Elab Term Command

def forInWithInvariant {m : Type → Type u₂} {α : Type v} [ForIn m (List α) α] {β : Type} [Monad m]
  (xs : List α) (init : β) (f : α → β → m (ForInStep β)) {ps : PredShape} [WP m ps] (_inv : PostCond (β × List.Zipper xs) ps) : m β :=
    pure () >>= fun _ => forIn xs init f

@[spec]
theorem Specs.forInWithInvariant_list {α : Type u} {β : Type} ⦃m : Type → Type v⦄ {ps : PredShape}
  [Monad m] [LawfulMonad m] [WP m ps] [WPMonad m ps]
  {xs : List α} {init : β} {f : α → β → m (ForInStep β)}
  {inv : PostCond (β × List.Zipper xs) ps}
  (step : ∀ b rpref x suff (h : xs = rpref.reverse ++ x :: suff),
      ⦃inv.1 (b, ⟨rpref, x::suff, by simp[h]⟩)⦄
      f x b
      ⦃(fun r => match r with
                 | .yield b' => inv.1 (b', ⟨x::rpref, suff, by simp[h]⟩)
                 | .done b' => inv.1 (b', ⟨xs.reverse, [], by simp⟩), inv.2)⦄) :
  ⦃inv.1 (init, ⟨[], xs, by simp⟩)⦄ forInWithInvariant xs init f inv ⦃(fun b => inv.1 (b, ⟨xs.reverse, [], by simp⟩), inv.2)⦄ := by
  simp only [forInWithInvariant, pure_bind]
  exact Specs.forIn_list inv step

syntax "assert " withPosition(basicFun) : doElem
syntax "invariant " withPosition(basicFun) : doElem

abbrev requiresGadget {α : Type} {m : Type → Type u} {ps : PredShape} [WP m ps] (_p : PreCond ps) (x : m α) : m α :=
  x

abbrev ensuresGadget {α : Type} {m : Type → Type u} {ps : PredShape} [WP m ps] (_p : α → PreCond ps) (x : m α): m α :=
  x

@[wp_simp]
theorem requiresGadget_apply [WP m sh] (x : m α) :
  wp⟦requiresGadget P x⟧.apply Q = wp⟦x⟧.apply Q := rfl

@[wp_simp]
theorem ensuresGadget_apply [WP m sh] (x : m α) :
  wp⟦ensuresGadget P x⟧.apply Q = wp⟦x⟧.apply Q := rfl

def assertGadget {m : Type → Type u} {ps : PredShape} [Monad m] [WP m ps] (_p : PreCond ps) : m Unit :=
  pure ()

def invariantGadget {m : Type → Type u} {ps : PredShape} [Monad m] [WP m ps] (_inv : PostCond (β × List.Zipper xs) ps) : m Unit :=
  pure ()

@[wp_simp]
theorem assertGadget_apply [Monad m] [WP m sh] : -- (h : PreCond.pure True ≤ P) :
  wp⟦assertGadget P : m Unit⟧.apply Q = wp⟦pure () : m Unit⟧.apply Q := rfl

@[wp_simp]
theorem invariantGadget_apply  {m : Type → Type u₂} {α : Type v} [ForIn m (List α) α] {β : Type} [Monad m] [LawfulMonad m]
  (xs : List α) (init : β) (f : α → β → m (ForInStep β)) {ps : PredShape} [WP m ps] [WPMonad m ps] (inv : PostCond (β × List.Zipper xs) ps) (Q : PostCond β ps) :
  wp⟦invariantGadget inv : m Unit⟧.apply (fun _ => wp⟦forIn xs init f⟧.apply Q, Q.2) = wp⟦forInWithInvariant xs init f inv⟧.apply Q := by
    calc
      _ = wp⟦invariantGadget inv >>= fun _ => forIn xs init f⟧.apply Q := by simp
      _ = wp⟦forInWithInvariant xs init f inv⟧.apply Q := rfl

macro_rules
  | `(doElem| assert $xs* => $p) => `(doElem| assertGadget (fun $xs* => $p))
  | `(doElem| invariant $xs* => $p) => `(doElem| invariantGadget (fun $xs* => $p))

-- syntax (name := spec)
--   ("requires " withPosition(basicFun))?
--   "ensures " withPosition(basicFun)
--   ("signals " withPosition(basicFun))* :
-- --  optSemicolon("specification_by " Tactic.tacticSeqIndentGt)?) : term

def spec : Parser := leading_parser
  optional ("forall " >> withPosition (many1 (ppSpace >> (Term.binderIdent <|> bracketedBinder))))
  >> optional ("requires " >> withPosition basicFun)
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

macro "CHONK" : tactic =>
  `(tactic| ((try intros); xstart; intro h; xwp; try (all_goals simp_all)))
--  `(tactic| sorry)

def Specification.specificationBy := leading_parser
  "specification_by " >>
  optional (atomic (many (ppSpace >> Term.binderIdent) >> " => ")) >>
  termParser

def Specification.suffix := leading_parser
  optional (ppDedent ppLine >> specificationBy)

def newdeclValSimple    := leading_parser
  -- " :=" >> ppHardLineUnlessUngrouped >> declBody >> Termination.suffix >> optional Term.whereDecls
  " :=" >> ppHardLineUnlessUngrouped >> declBody >> Termination.suffix >> optional Term.whereDecls >> Specification.suffix

@[builtin_doc] def newdeclVal :=
  -- Remark: we should not use `Term.whereDecls` at `declVal`
  -- because `Term.whereDecls` is defined using `Term.letRecDecl` which may contain attributes.
  -- Issue #753 shows an example that fails to be parsed when we used `Term.whereDecls`.
  withAntiquot (mkAntiquot "declVal" decl_name% (isPseudoKind := true)) <|
    newdeclValSimple <|> declValEqns <|> whereStructInst

def newdefinition     := leading_parser
  -- "def " >> recover declId skipUntilWsOrDelim >> ppIndent optDeclSig >> declVal >> optDefDeriving
  "def " >> recover declId skipUntilWsOrDelim >> ppIndent optDeclSig >> ppIndent spec >> newdeclVal >> optDefDeriving

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
  let spec := defn[3]
  let foralls? := if spec[0].isMissing then none else some spec[0][1].getArgs
  let requires? := spec[1]
  let ensures_ := Syntax.node2 SourceInfo.none nullKind spec[2] spec[3]
  -- dbg_trace requires?
  -- dbg_trace ensures_
  let refinedDecl1 := defn[1].setArg 0 <| match defn[1][0] with
    | .ident info ss val _ => Syntax.ident info ss (val ++ Name.mkSimple "refined") []
    | _ => panic "die" -- TODO
  -- dbg_trace defn[2][0]
  let optDeclSig := match defn[2].isMissing, foralls? with
    | _,  none => defn[2]
    | false, some bndrs => defn[2].setArg 0 (defn[2][0].setArgs (defn[2][0].getArgs ++ bndrs))
    | true, some bndrs => panic "die also"  -- TODO
  let numProgBinders : Nat := if defn[2].isMissing then 65536 else defn[2][0].getNumArgs
  unless defn[4].getKind == ``newdeclValSimple do throwUnsupportedSyntax
  let olddeclValRefined ← match defn[4] with
    | .node info ``newdeclValSimple args => do
      let req : TSyntax ``basicFun := ⟨requires?[1]⟩
      let ens : TSyntax ``basicFun := ⟨ensures_[1]⟩
      -- defn[4][1] is the term/do block; we'll patch it with the gadgets for requires and ensures
      let refinedDecl41 ← `(requiresGadget (fun $req:basicFun) (ensuresGadget (fun $ens:basicFun) $(⟨defn[4][1]⟩)))
      pure (Syntax.node info ``declValSimple (Array.set! args[:args.size-1] 1 refinedDecl41))
    | _ => throwUnsupportedSyntax
  -- dbg_trace olddeclValRefined
  let olddefn := Syntax.node5 stxinfo ``Parser.Command.definition defn[0] refinedDecl1 optDeclSig olddeclValRefined defn[5]
  let olddecl := Syntax.node2 declinfo ``Parser.Command.declaration decl[0] olddefn
 -- dbg_trace olddecl
  elabDeclaration olddecl
  let ns ← getCurrNamespace
  let declId := ns ++ declId
  let refinedDeclId := declId ++ Name.mkSimple "refined"
  let .some (.defnInfo defn) := (← getEnv).find? refinedDeclId | throwUnsupportedSyntax
--  log defn.name
--  dbg_trace defn.value
--  log defn.name
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
--    dbg_trace body
    let P ←
      if requires?.isMissing then pure none
      else do
        let_expr requiresGadget _α _m _ps _WP P body' := body | throwError "no requiresGadget"
        body := body'
        pure (some P)
    let_expr ensuresGadget α m ps wp Q body := body | throwError "no ensuresGadget"
    let some u := Level.dec (← getLevel (mkApp m α)) | throwError "invalid level (0?)"
    dbg_trace u
    let Q := mkApp3 (mkConst ``PostCond.total [.zero]) α ps Q
    let P := P.getD (mkApp2 (mkConst ``PreCond.pure) ps (mkConst ``True))
    -- dbg_trace P
    -- dbg_trace Q
    -- dbg_trace body
    -- unfold assertGadget and invariantGadget applications
    let pure_unit ← elabTerm (← `(pure ())) (some (mkApp m (mkConst ``Unit)))
    body := body.replace fun e => match_expr e with
      | assertGadget m _ _ _ _ => some pure_unit
      | invariantGadget m _ _ _ _ _ _ _ => some pure_unit
      | _ => none
    -- dbg_trace body
    -- spec := leading_parser
    --  "forall " (Term.binderIdent <|> bracketedBinder)+ ("requires" basicFun)? "ensures" basicFun ("signals" basicFun)*
    -- let `($xs => $e) := spec[0]
    -- dbg_trace spec[2][1]
    -- dbg_trace call
    let refined_triple_ty := mkApp7 (mkConst ``triple [u]) m ps wp α call P Q
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
  dbg_trace erased_spec
  let levelParams := collectLevelParams {} erased_spec |>.params
  dbg_trace levelParams

--  let refined_spec ← instantiateMVars (← spec_ty (← mkConstWithFreshMVarLevels defn.name) defn.type)
  let val := (← Term.elabTerm (← `(by unfold $(TSyntax.mk (mkIdent refinedDeclId)); CHONK)) (.some refined_spec) (catchExPostpone := false))
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

def mkFreshInt {m : Type → Type} [Monad m] : StateT (Nat × Nat) m Nat
  forall {ps} [WP m ps] [LawfulMonad m] [WPMonad m ps] n o
  requires s => PreCond.pure (s.1 = n ∧ s.2 = o)
  ensures r s => PreCond.pure (r = n ∧ s.1 = n + 1 ∧ s.2 = o)
:= do
  let n ← Prod.fst <$> get
  -- assert _ => PreCond.pure (o = 13)
  modify (fun s => (s.1 + 1, s.2))
  pure n

#print mkFreshInt.spec

example [WP m ps] [Monad m] [LawfulMonad m] [WPMonad m ps] : mkFreshInt (m:=m) = mkFreshInt.refined (m:=m) n o := rfl

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

def fib_spec : Nat → Nat
| 0 => 0
| 1 => 1
| n+2 => fib_spec n + fib_spec (n+1)

def fib_impl (n : Nat) : Idd Nat
--  ensures r => r = fib_spec n
:= do
  if n = 0 then return 0
  let mut a := 0
  let mut b := 1
  -- invariant xs => a = fib_impl xs.rpref.length ∧ b = fib_impl (xs.rpref.length + 1)
  for _ in [1:n] do
    let a' := a
    a := b
    b := a' + b
  return b

theorem fib_correct {n} : (fib_impl n).run = fib_spec n := by
  generalize h : (fib_impl n).run = x
  apply Idd.by_wp h
  unfold fib_impl
  xwp
  if h : n = 0 then simp[h,fib_spec] else ?_
  simp[h]
  xapp Specs.forIn_list ?inv ?step
  case inv => exact PostCond.total fun (⟨a, b⟩, xs) => a = fib_spec xs.rpref.length ∧ b = fib_spec (xs.rpref.length + 1)
  case pre => simp +arith +decide [Nat.succ_le_of_lt, Nat.zero_lt_of_ne_zero h, Nat.sub_sub_eq_min]
  case step =>
    intro ⟨a, b⟩ _pref x suff _h ⟨ha, hb⟩
    xwp
    simp_all[fib_spec]
  intro y ⟨_, hb⟩
  simp [Nat.sub_one_add_one h, hb]


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
