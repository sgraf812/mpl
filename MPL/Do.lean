import Lean
import MPL.WPMonad
import MPL.Triple
import MPL.Tactic

namespace MPL

open Lean Parser Meta Elab Term Command

syntax "assert " withPosition(basicFun) : doElem
syntax "invariant " withPosition(basicFun) : doElem

def requiresHelper {α : Type} {m : Type → Type u} {ps : PredShape} [Monad m] [WP m ps] (_p : PreCond ps) (x : m α) : m α :=
  x

def ensuresHelper {α : Type} {m : Type → Type u} {ps : PredShape} [Monad m] [WP m ps] (_p : α → PreCond ps) (x : m α): m α :=
  x

def assertHelper {m : Type → Type u} {ps : PredShape} [Monad m] [WP m ps] (_p : PreCond ps) : m Unit :=
  pure ()

def invariantHelper {m : Type → Type u} {ps : PredShape} [Monad m] [WP m ps] (_inv : PostCond (β × List.Zipper xs) ps) : m Unit :=
  pure ()

macro_rules
  | `(doElem| assert $xs* => $p) => `(doElem| assertHelper (fun $xs* => $p))
  | `(doElem| invariant $xs* => $p) => `(doElem| invariantHelper (fun $xs* => $p))

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

def forInWithInvariant {m : Type → Type u₂} {α : Type v} [ForIn m (List α) α] {β : Type} [Monad m]
  (xs : List α) (init : β) (f : α → β → m (ForInStep β)) {ps : PredShape} [WP m ps] (_inv : PostCond (β × List.Zipper xs) ps) : m β :=
    forIn xs init f

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
  ⦃inv.1 (init, ⟨[], xs, by simp⟩)⦄ forInWithInvariant xs init f inv ⦃(fun b => inv.1 (b, ⟨xs.reverse, [], by simp⟩), inv.2)⦄ :=
  Specs.forIn_list inv step

macro "CHONK" : tactic =>
  `(tactic| (intros; intro h; xwp; all_goals simp_all))

def newdefinition     := leading_parser
  -- "def " >> recover declId skipUntilWsOrDelim >> ppIndent optDeclSig >> declVal >> optDefDeriving
  "def " >> recover declId skipUntilWsOrDelim >> ppIndent optDeclSig >> ppIndent spec >> declVal >> optDefDeriving

@[command_parser]
def newdeclaration := leading_parser
  declModifiers false >> newdefinition

@[command_elab newdeclaration]
partial def elab_newdecl : CommandElab := fun stx => do
  -- newdeclaration := declModifiers false >> newdefinition
  -- newdefinition := "def " >> recover declId skipUntilWsOrDelim >> ppIndent optDeclSig >> ppIndent spec >> declVal >> optDefDeriving
  let decl     := stx[1]
  let declKind := decl.getKind
  let declId := decl[1][0].getId
  let some stxinfo := stx.getInfo? | throwUnsupportedSyntax
  let some declinfo := decl.getInfo? | throwUnsupportedSyntax
--  dbg_trace decl
--  dbg_trace stx
--  dbg_trace stx.getNumArgs
  let spec := decl[3]
  let foralls? := if spec[0].isMissing then none else some spec[0][1].getArgs
  let requires? := spec[1]
  let ensures_ := Syntax.node2 SourceInfo.none nullKind spec[2] spec[3]
  -- dbg_trace requires?
  -- dbg_trace ensures_
  let refinedDecl1 := decl[1].setArg 0 <| match decl[1][0] with
    | .ident info ss val _ => Syntax.ident info ss (val ++ Name.mkSimple "refined") []
    | _ => panic "die" -- TODO
  -- dbg_trace decl[2][0]
  let optDeclSig := match decl[2].isMissing, foralls? with
    | _,  none => decl[2]
    | false, some bndrs => decl[2].setArg 0 (decl[2][0].setArgs (decl[2][0].getArgs ++ bndrs))
    | true, some bndrs => panic "die also"  -- TODO
  unless decl[4].getKind == ``declValSimple do throwUnsupportedSyntax
  let req : TSyntax ``basicFun := ⟨requires?[1]⟩
  let ens : TSyntax ``basicFun := ⟨ensures_[1]⟩
  -- decl[4][1] is the term/do block
  let refinedDecl41 ← `(requiresHelper (fun $req:basicFun) (ensuresHelper (fun $ens:basicFun) $(⟨decl[4][1]⟩)))
  -- let refinedDecl41 ← `(ensuresHelper (fun _ _ => PreCond.pure True) ($(⟨decl[4][1]⟩)))
  -- dbg_trace refinedDecl41
  let olddecl := Syntax.node5 stxinfo ``Parser.Command.definition decl[0] refinedDecl1 optDeclSig (decl[4].setArg 1 refinedDecl41) decl[5]
  let oldstx := Syntax.node2 declinfo ``Parser.Command.declaration stx[0] olddecl
 -- dbg_trace oldstx
  elabDeclaration oldstx
  let ns ← getCurrNamespace
  let declId := ns ++ declId
  let .some (.defnInfo defn) := (← getEnv).find? (declId ++ Name.mkSimple "refined") | throwUnsupportedSyntax
--  log defn.name
--  dbg_trace defn.value
--  log defn.name
  runTermElabM fun vars => do
  let rec spec_ty (prog : Expr) : (ty : Expr) → TermElabM Expr
    | .forallE x ty body_ty info => withLocalDecl x info ty fun a => do
      let spec ← spec_ty (mkApp prog a) (body_ty.instantiate1 a)
      return ← mkForallFVars #[a] spec
    | ty => do
    let .app m α := ty | throwUnsupportedSyntax
    let ps ← mkFreshExprMVar (mkConst ``PredShape) (userName := `ps)
    let u ← mkFreshLevelMVar
    let wp ← synthInstance (mkApp2 (mkConst ``MPL.WP [u]) m ps)
    -- spec := leading_parser
    --  "forall " (Term.binderIdent <|> bracketedBinder)+ ("requires" basicFun)? "ensures" basicFun ("signals" basicFun)*
    -- let `($xs => $e) := spec[0]
    -- dbg_trace spec[2][1]
    dbg_trace prog
--    let P ←
--      if spec[0].isMissing then pure (mkApp2 (mkConst ``PreCond.pure) ps (mkConst ``True))
--      else elabTerm (← `(fun $xs* => $e)) (mkApp (mkConst ``PreCond) ps)
--    let xs : TSyntaxArray ``funBinder := TSyntaxArray.mk spec[3][0].getArgs
--    let optType := spec[3][1]
--    let e : TSyntax `term := ⟨spec[3][3]⟩
--    let Q ← elabTerm (← `((fun $xs* => $e, FailConds.false))) (mkApp2 (mkConst ``PostCond [u]) α ps)
    let triple_ty := mkApp7 (mkConst ``triple [u]) m ps wp α prog sorry sorry
--    let triple_ty ← mkForallFVars fvars triple_ty
    return triple_ty
  let spec ← instantiateMVars (← spec_ty (mkConst defn.name (defn.levelParams.map .param)) defn.type)
--  let spec ← instantiateMVars (← spec_ty (← mkConstWithFreshMVarLevels defn.name) defn.type)
  let val := (← Term.elabTerm (← `(by unfold $(TSyntax.mk (mkIdent declId)); CHONK)) (.some spec) (catchExPostpone := false))
  synthesizeSyntheticMVarsNoPostponing
  let val ← instantiateMVars val
  -- dbg_trace spec.hasLevelMVar
  -- dbg_trace val.hasLevelMVar
  addDecl (.thmDecl {
    name := declId ++ Name.mkSimple "spec"
    levelParams := defn.toConstantVal.levelParams
    type := spec
    -- value := ← Term.elabTermEnsuringType (← `(by sorry)) spec
    value := val
  })

def mkFreshInt {m : Type → Type} [Monad m] : StateT (Nat × Nat) m Nat
  forall {sh} [WP m sh] [LawfulMonad m] [WPMonad m sh] n o
  requires s => PreCond.pure (s.1 = n ∧ s.2 = o)
  ensures r s => PreCond.pure (r = n ∧ s.1 = n + 1 ∧ s.2 = o)
:= do
  let n ← Prod.fst <$> get
  -- assert PreCond.pure (n = 13)
  modify (fun s => (s.1 + 1, s.2))
  pure n

#print mkFreshInt.spec

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
  ensures r => r = fib_spec n
:= do
  if n = 0 then return 0
  let mut a := 0
  let mut b := 1
  invariant xs => a = fib_impl xs.rpref.length ∧ b = fib_impl (xs.rpref.length + 1)
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
