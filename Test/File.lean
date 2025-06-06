import MPL

open MPL

set_option grind.warning false

@[grind →]
theorem range_elim : List.range' s n = xs ++ i :: ys → i = s + xs.length := by
  intro h
  induction xs generalizing s n
  case nil => cases n <;> simp_all[List.range']
  case cons head tail ih =>
    cases n <;> simp[List.range'] at h
    have := ih h.2
    simp[ih h.2]
    omega

@[simp]
theorem Array.extract_min_stop_size {xs : Array α} :
    xs.extract 0 (min stop xs.size) = xs.extract 0 stop := by
  ext i h₁ h₂
  · simp
  · simp

@[simp]
theorem Array.extract_push_2 {xs : Array α} (h : xs.size ≤ start) :
    ((xs.push x).extract start stop) = #[x].extract (start - xs.size) (stop - xs.size) := by
  ext i h₁ h₂
  · simp
    grind
  · simp_all [getElem_push]
    grind

@[simp]
theorem Array.extract_complete {v : Vector α n} :
    Array.extract v.toArray 0 n = v.toArray := by simp

theorem Array.extract_set' {xs : Array α} (hxs : m < xs.size) :
    (xs.set m v).extract i m = xs.extract i m := by
  grind

theorem Array.extract_add_one {xs : Array α} (h₁ : i ≤ j) (h₂ : j < xs.size) :
    (xs.extract i (j + 1)) = (xs.extract i j).push xs[j] := by
  simp [h₁]

theorem Array.extract_sub_n {xs : Array α} (h : n < xs.size) (h₂ : xs.size > 0) :
    xs.extract (xs.size - (n+1)) = #[xs[xs.size - (n+1)]] ++ xs.extract (xs.size - n) := by
  ext i h₁ h₂
  · grind
  · simp; grind

theorem Array.extract_split_last {xs ys : Array α} (h₁ : xstart ≤ xend) (h₂ : ystart ≤ yend) (hxs : xend < xs.size) (hys : yend < ys.size) :
    (xs.extract xstart xend = ys.extract ystart yend) → xs[xend] = ys[yend] →
    xs.extract xstart (xend + 1) = ys.extract ystart (yend + 1) := by
  grind [Array.extract_add_one]

namespace Mem
def Mem := Array UInt8
def MemPos := Int

inductive MemError where
  | invalidPos

abbrev MemM := EStateM MemError Mem

abbrev Mem.validPos (f : Mem) (p : MemPos) : Prop :=
  @LE.le Int _ 0 p ∧ @LT.lt Nat _ p.toNat (f : Array UInt8).size

def Mem.peek? (pos : MemPos) : MemM (Option UInt8) := do
  return @getElem? (Array UInt8) Nat UInt8 _ _ (← get) pos.toNat

def Mem.peek! (p : MemPos) : MemM UInt8 := do
  match (← peek? p) with
  | some b => return b
  | none => throw MemError.invalidPos

def Mem.poke (pos : MemPos) (b : UInt8) : MemM PUnit := do
  let f ← get
  if h : f.validPos pos then
    @set Mem _ _ (f.set pos.toNat b h.2)
  else
    throw MemError.invalidPos

def MemPos.add (p : MemPos) (offs : Int) : MemPos :=
  @HAdd.hAdd Int Int Int _ p offs
end Mem

structure File where
  bytes : Array UInt8
  pos : Fin (bytes.size + 1)
  deriving Inhabited

abbrev File.mkEmpty : File := { bytes := Array.mkEmpty 0, pos := ⟨0, by simp⟩ }

inductive FileError where
  | invalidPos
  | invalidFormat
  | eof

def File.append (f : File) (bs : Array UInt8) : File :=
  { f with bytes := f.bytes ++ bs, pos := f.pos.castLE (by simp) }

@[simp]
theorem File.append_bytes : (File.append f bs).bytes = f.bytes ++ bs := rfl

@[simp]
theorem File.append_pos : (File.append f bs).pos = f.pos.castLE (by simp) := rfl

abbrev FileM := EStateM FileError File

namespace FileM

def read (nbytes : Nat) : FileM (Vector UInt8 nbytes) := do
  let f ← get
  let mut ret := Vector.replicate nbytes default
  let mut pos := f.pos
  for h₁ : i in [:nbytes] do
    if h₂ : pos < f.bytes.size then
      ret := ret.set i f.bytes[pos]
      pos := pos.succ.castLT (by simp [h₂])
    else
      throw FileError.eof
  set { f with pos := pos }
  return ret

def append (bytes : Array UInt8) : FileM PUnit :=
  modify (·.append bytes)

def tell : FileM Nat := do
  let f ← get
  return f.pos.val

def seek (pos : Nat) : FileM PUnit := do
  let f ← get
  if h : pos < f.bytes.size + 1 then
    set { f with pos := ⟨pos, h⟩ }
  else
    throw FileError.eof

def move (offs : Int) : FileM PUnit := do
  let f ← get
  let pos := f.pos.val + offs
  if h : 0 ≤ pos ∧ pos.toNat < f.bytes.size + 1 then
    set { f with pos := ⟨pos.toNat, h.2⟩ }
  else
    throw FileError.invalidPos

theorem wp_append : wp⟦FileM.append bs⟧ Q f = Q.1 () (f.append bs) := by
  simp [wp, append, modify, modifyGet, EStateM.instMonadStateOf, EStateM.modifyGet]

def canRead (n : Nat) (f : File) : Prop :=
  f.pos + n ≤ f.bytes.size

theorem canRead_mono {n m : Nat} (hn : n ≤ m) :
    SPred.entails (σs:=[File]) (canRead m) (canRead n) := by
  intro f
  simp[canRead]
  intro h
  omega

def hasRead {n : Nat} (v : Vector UInt8 n) (oldF newF : File) : Prop :=
  oldF.bytes = newF.bytes ∧ oldF.pos + n = newF.pos  ∧ oldF.bytes.extract oldF.pos newF.pos = v.toArray

theorem read_spec_manual :
    ⦃fun f' => ⌜canRead n f' ∧ f' = f⌝⦄
    FileM.read n
    ⦃⇓ v f' => hasRead v f f'⦄ := by
  mintro h ∀f'
  mpure h
  have ⟨hread, hfile⟩ := h
  subst hfile
  unfold FileM.read
  dsimp only [get, getThe]
  mspec
  mspec
  case inv => exact ⇓ (⟨pos, buf⟩, xs) =>
    ⌜pos = f'.pos + xs.pref.length ∧ pos + xs.suff.length ≤ f'.bytes.size
    ∧ f'.bytes.extract f'.pos pos = (buf.take xs.pref.length).toArray⌝
  case pre1 => intro hread; simp_all[canRead]; omega
  case step =>
    intro ⟨pos, buf⟩ pref i hi suff hsuff
    have := range_elim hsuff
    simp at this
    subst_vars
    mintro ⌜hinv⌝
    simp at hinv
    dsimp
    split
    · mspec
      mspec
      mpure_intro
      simp +arith [hinv]
      sorry -- pure proof about offset arithmetic and Array.extract
    · grind
  case post.except => simp
  mintro ∀f
  mspec
  cases r
  simp_all [canRead, hasRead]
  rw[← h.right.right]
  congr
  rw[← h.left]

@[spec]
theorem read_spec :
  ⦃fun f' => ⌜canRead n f' ∧ f' = f⌝⦄
  read n
  ⦃⇓ v f' => hasRead v f f'⦄
  := by
  mvcgen [read]
  case inv =>
    rename_i f'
    exact ⇓ (⟨pos, buf⟩, xs) =>
    ⌜pos = f'.pos + xs.pref.length ∧ pos + xs.suff.length ≤ f'.bytes.size
    ∧ f'.bytes.extract f'.pos pos = (buf.take xs.pref.length).toArray⌝
  all_goals simp_all
  case pre1 => simp_all +arith [canRead]; have := h.right.symm; subst this; grind
  case post.success =>
    rename_i hread _
    have := hread.right.symm
    subst this
    simp_all +arith [hasRead]
    grind
  case ifTrue =>
    -- read_spec_manual above omits this proof
    rename_i hread hx'
    have hx' := range_elim hx'
    simp at hx'
    subst hx'
    have := hread.right.symm
    subst this
    simp +arith
    intro ⟨hfst, hsuff, hextract⟩
    constructor
    · exact hfst ▸ hsuff
    · apply Array.extract_split_last <;> try simp_all
      · rw [Array.extract_set']
        exact hfst ▸ hextract
      · exact hx.upper
  case ifFalse => grind

end FileM

inductive Schema where
  | byte -- 1 byte
  | word -- 4 bytes, big endian (because)
  | enum (nalts : Nat) (h : nalts ≤ 256) (alts : Fin nalts → Schema)
--  | struct (nflds : Nat) (flds : Fin nflds → Schema)
  | array (elt : Schema)

def Pi.toTuple (n : Nat) (f : Fin n → Type) : Type := match n with
  | 0 => PUnit
  | n + 1 => f 0 × Pi.toTuple n (f ∘ Fin.succ)

abbrev Schema.interp (s : Schema) : Type := match s with
  | byte => UInt8
  | word => UInt32
  | enum nalts _ alts => Σ i : Fin nalts, (alts i).interp
--  | struct nflds flds => Pi.toTuple nflds (fun i => (flds i).interp)
  | array elt => Array (Schema.interp elt)

mutual
def Schema.parse (s : Schema) : FileM s.interp := do
  match s with
  | .byte => do
    let b ← FileM.read 1
    return b[0]
  | .word => do
    let bs ← FileM.read 4
    return ((bs[0].toUInt32 <<< 24) ||| (bs[1].toUInt32 <<< 16) ||| (bs[2].toUInt32 <<< 8) ||| bs[3].toUInt32)
  | .enum nalts _ alts => do
    let i ← FileM.read 1
    let tag := i[0]
    if h : tag.toNat < nalts
    then
      let tag := ⟨tag.toNat, h⟩
      return ⟨tag, ← (alts tag).parse⟩
    else throw FileError.invalidFormat
--  | .struct nflds flds => Pi.toTuple.parse nflds flds
  | .array elt => do
    let n ← FileM.read 1
    let n := n[0].toNat
    let mut ret := Array.mkEmpty n
    for i in [:n] do
      ret := ret.push (← elt.parse)
    return ret
decreasing_by (repeat sorry)

def Pi.toTuple.parse (n : Nat) (f : Fin n → Schema) : FileM (Pi.toTuple n (Schema.interp ∘ f)) :=
  match n with
  | 0 => return ()
  | n + 1 => do
    let hd ← (f 0).parse
    let tl ← Pi.toTuple.parse n (f ∘ Fin.succ)
    return (hd, tl)
decreasing_by (repeat sorry)
end

def Schema.serialize (s : Schema) (v : s.interp) : FileM PUnit := do
  match s, v with
  | byte, b => do
    FileM.append #[b]
  | word, w => do
    FileM.append (#[w >>> 24, w >>> 16, w >>> 8, w].map (·.toUInt8))
  | enum nalts h alts, ⟨tag, v⟩ => do
    FileM.append #[.ofBitVec (tag.castLE h)]
    (alts tag).serialize v
--  | struct nflds flds, t => do
--    match h : nflds with
--    | 0 => return ()
--    | nflds + 1 => do
--      (flds 0).serialize (t.fst)
--      (struct nflds (flds ∘ Fin.succ)).serialize t.snd
  | array elt, a => do
    FileM.append #[a.size.toUInt8]
    for (v : elt.interp) in (a : Array elt.interp) do
      elt.serialize v
decreasing_by (repeat sorry)

attribute [spec] FileM.append

theorem FileM.append_ok : ⦃⌜True⌝⦄ FileM.append bs ⦃⇓ () => ⌜True⌝⦄ := by
  mvcgen

theorem Schema.serialize_ok {s : Schema} (v : s.interp) :
  ⦃⌜True⌝⦄ s.serialize v ⦃⇓ () => ⌜True⌝⦄ := by
  induction s, v using Schema.serialize.induct <;> mvcgen [Schema.serialize, *]
  case inv => exact (⇓ _ => ⌜True⌝)
  all_goals simp_all

theorem serialize_ne_error {s : Schema} (v : s.interp) :
    s.serialize v File.mkEmpty ≠ .error e f := by
  have := Schema.serialize_ok v File.mkEmpty True.intro
  simp[wp, FailConds.false, FailConds.const] at this
  simp[this]
  intro h
  simp[h] at this

theorem serialize_ok_simple {s : Schema} (v : s.interp) :
    ∃ f, s.serialize v File.mkEmpty = .ok () f := by
  cases h : s.serialize v File.mkEmpty <;> simp_all [serialize_ne_error v]

@[simp]
def byteSize {s : Schema} (v : s.interp) : Nat :=
  match s, v with
  | .byte, _ => 1
  | .word, _ => 4
  | .enum _ _ _, ⟨_, v⟩ => 1 + byteSize v
--  | .struct 0 flds, t => 0
--  | .struct (n+1) flds, (e, t) => byteSize e + @byteSize (Schema.struct n (flds ∘ Fin.succ)) t
  | .array _, a => a.foldl (init := 0) (fun acc v => acc + byteSize v) + 1

theorem EStateM.wp_to_tuple {ε σ α} {x : EStateM ε σ α} {Q : PostCond α (.except ε (.arg σ .pure))} {s : σ}
  (h : wp⟦x⟧ Q s) : ⦃(· = s)⦄ x ⦃Q⦄ := by intro _ hs; subst hs; exact h

theorem serialize_byteSize {s : Schema} (v : s.interp) (oldf : File) :
  ⦃fun f' => oldf = f'⦄
  s.serialize v
  ⦃⇓ () f' => f'.bytes.size = byteSize v + oldf.bytes.size⦄ := by
  induction s, v using Schema.serialize.induct generalizing oldf <;> mvcgen [Schema.serialize, *]
  case inv => exact (⇓ (_, xs) f =>
    f.bytes.size = xs.pref.foldl (fun acc v => acc + byteSize v) 0 + oldf.bytes.size + 1)
  case step.pre1 => mpure_intro; rfl
  all_goals simp_all +arith

theorem Array.extract_sub {xs ys : Array α} (hsub : stop₁ ≤ stop₂) (h : xs.extract start stop₂ = ys) :
    xs.extract start stop₁ = ys.extract 0 (stop₁ - start) := by
  ext i h₁ h₂
  · grind
  · simp; grind

theorem serialize_history {s : Schema} (v : s.interp) (oldf : File) :
  ⦃fun f => oldf = f⦄
  s.serialize v
  ⦃⇓ () newf => newf.bytes.take oldf.bytes.size = oldf.bytes⦄ := by
  induction s, v using Schema.serialize.induct generalizing oldf <;> mvcgen [Schema.serialize]
  case case1 => simp_all
  case case2 => simp_all
  case case3 tag v ih oldf' =>
    mspec ih (oldf.append #[tag])
    case pre1 f => simp_all; rfl
    subst h
    intro newf h
    have := Array.extract_sub (stop₁ := oldf.bytes.size) (by simp) h
    simp at this
    simp_all
  case inv =>
    exact ⇓ (_, xs) newf => oldf.bytes = newf.bytes.take oldf.bytes.size
  case step ih oldf _ =>
    subst_vars
    simp_all
    mspec ih
    rename_i oldf'
    intro newf h₂
    rw [←h₂] at h
    simp [show oldf.bytes.size ≤ oldf'.bytes.size by rw [h]; simp; omega] at h
    exact h
  case pre1 => simp [h]
  case except => simp
  case success =>
    subst_vars
    simp
    intro h
    exact h.symm
  all_goals simp_all

abbrev serialized.Q {s : Schema} (v : s.interp) (f : File) : PostCond PUnit (.except FileError (.arg File .pure)) :=
  ⇓ _ newf =>
    f.pos + byteSize v ≤ f.bytes.size
    ∧ f.bytes.extract f.pos (f.pos + byteSize v) = newf.bytes.extract (newf.bytes.size - byteSize v) newf.bytes.size

def serialized {s : Schema} (v : s.interp) (f : File) : Prop :=
  ∀ oldf, wp⟦s.serialize v⟧ (serialized.Q v f) oldf

theorem Array.extract_size_eq {a : Array α} {start : Nat} :
    start ≤ a.size → (a.extract start (start + n)).size = n → start + n ≤ a.size := by
  simp +contextual +arith
  intro h
  omega

theorem serialized_canRead {s : Schema} (v : s.interp) (hn : n ≤ byteSize v):
    SPred.entails (σs:=[File]) (serialized v) (FileM.canRead n) := by
  apply SPred.entails.trans _ (FileM.canRead_mono hn)
  intro f
  simp [serialized, FileM.canRead]
  intro h
  replace h := h File.mkEmpty
  simp [wp] at h
  split at h; case h_2 => contradiction
  simp_all

/-
theorem serialized.Q.enum_mono {nalts : Nat} {h : nalts ≤ 256} {alts : Fin nalts → Schema} {tag : Fin nalts} (v : (alts tag).interp) (f : File) (start : File) :
    serialized.Q v f ⊢ₚ serialized.Q (s := .enum _ h _) ⟨tag, v⟩ (f.append #[tag]) := by
  simp only [PostCond.entails, byteSize, forall_const, FailConds.false, FailConds.const,
    FailConds.entails.refl, and_true]
  intro stop h
  simp +arith
  ext i h₁ h₂
  · simp +arith; sorry -- uff
  · simp
    by_cases h₀ : i = 0
    · simp_all

theorem serialized.Q.append' {nalts : Nat} {h : nalts ≤ 256} {alts : Fin nalts → Schema} {tag : Fin nalts} (v : (alts tag).interp) (f : File) (start : File) :
    wp⟦(alts tag).serialize v⟧ (serialized.Q v (f.append #[tag])) (start.append #[tag])
    → wp⟦(alts tag).serialize v⟧ (serialized.Q (s := .enum _ h _) ⟨tag, v⟩ f) (start.append #[tag]) := by
  simp [-Array.append_singleton, serialized.Q]
  intro h
  induction s, v using Schema.serialize.induct generalizing f start₁ start₂
  case case1 => simp_all [Schema.serialize, FileM.wp_append]
  case case2 => simp_all [Schema.serialize, FileM.wp_append]
  case case3 tag v ih =>
    simp_all [Schema.serialize, FileM.wp_append]
    apply ih f _ _ h

theorem serialized.Q.blah : wp⟦(alts✝ tag).serialize v⟧ (Q ⟨tag, v⟩ f) (start₁.append #[OfNat.ofNat ↑tag])

theorem serialized.Q.append {s : Schema} (v : s.interp) (f : File) (start₁ start₂ : File) :
    wp⟦s.serialize v⟧ (serialized.Q v f) start₁ → wp⟦s.serialize v⟧ (serialized.Q v f) start₂ := by
  intro h
  induction s, v using Schema.serialize.induct generalizing f start₁ start₂
  case case1 => simp_all [Schema.serialize, FileM.wp_append]
  case case2 => simp_all [Schema.serialize, FileM.wp_append]
  case case3 tag v ih =>
    simp_all [Schema.serialize, FileM.wp_append]
    apply ih f _ _ h

theorem serialized_of_some_file {s : Schema} (v : s.interp) (f : File) (somef : File):
  wp⟦s.serialize v⟧ (serialized.Q v f) somef
  → serialized v f := by
  simp [serialized]
  intro h oldf
  induction s, v using Schema.serialize.induct generalizing f oldf somef
  case case1 => simp_all [Schema.serialize, FileM.wp_append]
  case case2 => simp_all [Schema.serialize, FileM.wp_append]
  case case3 tag v ih =>
    simp_all [Schema.serialize, FileM.wp_append]
    let f' := f.append #[tag]
    let somef' := somef.append #[tag]
    simp_all [serialized.Q]
    conv at h in _ ∧ _ =>
      congr
      · rhs; rw [← Nat.add_assoc]; rw [show somef.bytes.size + 1 = somef'.bytes.size by simp [somef']]
      · rfl

    have := ih somef' h
    apply ih _ h
  all_goals
  simp [serialized] at h
  simp_all
  intro h
  subst h

@[simp]
theorem Array.extract_complete {v : Vector α n} :
    Array.extract v.toArray 0 n = v.toArray := by simp

theorem serialized_hasRead_byte {bs : Vector UInt8 1} {v : Schema.byte.interp} :
    serialized v f → hasRead bs f f' → v = bs[0] := by
  cases bs
  simp [serialized, hasRead, Schema.serialize, FileM.wp_append]
  intro hv hff' hpos harr
  subst harr
  simp
  rw [Array.extract_add_one] at hv
  simp only [Nat.le_refl, Array.extract_empty_of_stop_le_start, List.push_toArray_fun,
    List.nil_append_fun, id_def] at hv
  injection hv with hv
  case h₁ => grind
  case h₂ => grind
  simp at hv
  injection hv with hv
  simp_all only

theorem serialized_hasRead_word {bs : Vector UInt8 4} {v : Schema.word.interp} :
    serialized v f → hasRead bs f f' → v = ((bs[0].toUInt32 <<< 24) ||| (bs[1].toUInt32 <<< 16) ||| (bs[2].toUInt32 <<< 8) ||| bs[3].toUInt32) := by
  cases bs with | mk arr =>
  simp [serialized, hasRead, Schema.serialize, FileM.wp_append]
  intro hbuf hff' hpos harr
  have hix : ↑f.pos + 3 < f.bytes.size := by grind
  simp +arith (discharger := omega) [Array.extract_sub_n] at hbuf
  subst harr
  simp_all [Nat.le_refl, Array.extract_empty_of_stop_le_start, List.push_toArray,
    List.nil_append, List.cons_append, Array.mk.injEq, List.cons.injEq, and_true,
    Array.getElem_extract, Nat.add_zero, UInt32.toUInt32_toUInt8]
  bv_decide

theorem serialized_hasRead_enum {alts : Fin nalts → Schema} {bs : Vector UInt8 1} {v : (alts tag).interp} :
    serialized (s := .enum nalts _ alts) ⟨tag, v⟩ f → hasRead bs f f' → tag = bs[0] ∧ serialized v (f.append #[tag]) ∧ hasRead bs (f.append #[tag]) f' := by
  simp [serialized, hasRead, Schema.serialize, FileM.wp_append]
  intro hser
  wp_simp
  simp_all
  intro _ hv hbytes hpos hbs
  cases bs
  simp_all
-/

theorem blah {s : Schema} (v : s.interp) :
    ⦃serialized v⦄
    s.parse
    ⦃⇓ v' => ⌜v = v'⌝⦄ := by
  mintro hser
  mhave hcanRead : FileM.canRead (byteSize v) := serialized_canRead v .refl
  induction s using Schema.parse.induct <;> mvcgen [Schema.parse, *]
  case case1.pre1 =>
    mpure_intro
    refine ⟨h.right, rfl⟩
  case case1.post f =>
    intro f' hread
    simp only [SVal.curry_cons, SVal.curry_nil]
    rcases h with ⟨hser, hread⟩
    cases r
    -- Doing it in one go loses info on `v`?!
--    simp_all only [serialized, EStateM.instWP, Schema.serialize, FileM.append, modify, modifyGet,
--      EStateM.instMonadStateOf, FailConds.pure_def, EStateM.modifyGet, byteSize, SPred.and_nil,
--      File.append_bytes, Array.append_singleton, Array.size_push, Nat.add_eq_right,
--      Array.size_eq_zero_iff, hasRead]
    simp_all only [serialized, Schema.serialize, FileM.append, modify, modifyGet,
      EStateM.instMonadStateOf, FailConds.pure_def, byteSize, SPred.and_nil, FileM.hasRead,
      Vector.getElem_mk]
    simp_all only [EStateM.instWP, EStateM.modifyGet, File.append_bytes, Array.append_singleton,
      Array.size_push, Nat.add_eq_right, Array.size_eq_zero_iff]
    replace hser := hser f
    simp (discharger := omega) [Array.extract_add_one, Array.extract_empty_of_stop_le_start] at hser
    simp [← hread.right, hread.left]
    simp_all
  case case2.pre1 =>
    mpure_intro
    refine ⟨h.right, rfl⟩
  case case2.post f =>
    intro f' hread
    simp only [SVal.curry_cons, SVal.curry_nil]
    rcases h with ⟨hser, hread⟩
    cases r
    -- Doing it in one go loses info on `v`?!
--    simp_all only [serialized, EStateM.instWP, Schema.serialize, FileM.append, modify, modifyGet,
--      EStateM.instMonadStateOf, FailConds.pure_def, EStateM.modifyGet, byteSize, SPred.and_nil,
--      File.append_bytes, Array.append_singleton, Array.size_push, Nat.add_eq_right,
--      Array.size_eq_zero_iff, hasRead]
    simp_all only [serialized, Schema.serialize, FileM.append, modify, modifyGet,
      EStateM.instMonadStateOf, FailConds.pure_def, byteSize, SPred.and_nil, FileM.hasRead,
      Vector.getElem_mk]
    simp_all only [EStateM.instWP, EStateM.modifyGet, File.append_bytes, Array.append_singleton,
      Array.size_push, Nat.add_eq_right, Array.size_eq_zero_iff]
    replace hser := hser f
    simp (discharger := omega) [Array.extract_add_one, Array.extract_empty_of_stop_le_start] at hser
    simp [← hread.right, hread.left]
    simp_all
  case case1.ifTrue =>
    simp_all only [hasRead, serialized, Schema.serialize, FileM.append, modify, modifyGet, instMonadStateOf]
    exact serialized_hasRead_enum hser hread
  case case1.ifFalse =>
    simp_all only [hasRead, serialized, Schema.serialize, FileM.append, modify, modifyGet, instMonadStateOf]
    exact serialized_hasRead_enum hser hread
  case case2 => sorry
/-
  case case1 =>
    unfold Schema.parse
    mintro ∀f
    mpure hser
    mwp
    mspec read_spec
    case pre => mpure_intro; refine ⟨?_, rfl⟩; apply serialized_canRead _ .refl _ hser
  case case2 =>
    unfold Schema.parse
    mintro ∀f
    mpure hser
    mwp
    mspec read_spec
    case pre => mpure_intro; refine ⟨?_, rfl⟩; apply serialized_canRead _ .refl _ hser
    case post.success => intro f hread; exact serialized_hasRead_word hser hread
  case case3 =>
    unfold Schema.parse
    mintro ∀f
    mpure hser
    mwp
    mspec read_spec
    case pre => mpure_intro; refine ⟨?_, rfl⟩; apply serialized_canRead _ (by simp) _ hser
    case post.success => intro f hread; exact serialized_hasRead_byte hser hread
-/
