import MPL
import MPL.ProofMode.Tactics.VCGen

open MPL

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

def File.mkEmpty : File := { bytes := Array.mkEmpty 0, pos := ⟨0, by simp⟩ }

inductive FileError where
  | invalidPos
  | invalidFormat
  | eof

def File.append (f : File) (bs : Array UInt8) : File :=
  { f with bytes := f.bytes ++ bs, pos := f.pos.castLE (by simp) }

@[simp]
theorem File.append_bytes : (File.append f bs).bytes = f.bytes ++ bs := rfl

abbrev FileM := EStateM FileError File

namespace FileM

def read (nbytes : Nat) : FileM (Vector UInt8 nbytes) := do
  let f ← get
  let mut ret := Vector.mkVector nbytes default
  let mut pos := f.pos
  for h₁ : i in [:nbytes] do
    if h₂ : pos < f.bytes.size then
      ret := ret.set i f.bytes[pos]
      pos := pos.succ.castLT (by simp[h₂])
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
  induction s, v using Schema.serialize.induct generalizing oldf
  case case1 => mvcgen [Schema.serialize]; simp +contextual +arith
  case case2 => mvcgen [Schema.serialize]; simp +contextual +arith
  case case3 ih => mvcgen [Schema.serialize, *]; simp_all; omega
  case case4 arr ih =>
    mvcgen [Schema.serialize, *]
    case inv => exact (⇓ ((), xs) f =>
      f.bytes.size = xs.pref.foldl (fun acc v => acc + byteSize v) 0 + oldf.bytes.size + 1)
    simp [*]
    case pre1.post.success => simp +contextual +arith
    case pre1.post.except => simp
    case step.post.success => simp
    case step => simp; set_option trace.Meta.isDefEq true in rfl

theorem serialize_byteSize' {s : Schema} (v : s.interp) (oldf : File) :
  ⦃fun f' => oldf = f'⦄
  s.serialize v
  ⦃⇓ () f' => f'.bytes.size = byteSize v + oldf.bytes.size⦄ := by
  induction s, v using Schema.serialize.induct generalizing oldf <;> mvcgen [Schema.serialize, *]
  case case1 => simp +contextual +arith
  case case2 => simp +contextual +arith
  case case3 ih => simp_all; omega
  case inv => exact (⇓ ((), xs) f =>
    f.bytes.size = xs.pref.foldl (fun acc v => acc + byteSize v) 0 + oldf.bytes.size + 1)
  all_goals simp +arith +contextual [*]


def serialized {s : Schema} (v : s.interp) (f : File) : Prop :=
  wp⟦s.serialize v⟧
    (⇓ _ f' => f'.bytes.size = byteSize v ∧ f.bytes.extract f.pos.val (f.pos.val + byteSize v) = f'.bytes)
    File.mkEmpty

def canRead (n : Nat) (f : File) : Prop :=
  f.pos + n ≤ f.bytes.size

def hasRead {n : Nat} (v : Vector UInt8 n) (oldF newF : File) : Prop :=
  oldF.bytes = newF.bytes ∧ oldF.pos + n = newF.pos  ∧ oldF.bytes.extract oldF.pos newF.pos = v.toArray

theorem Array.extract_size_eq {a : Array α} {start : Nat} :
    start ≤ a.size → (a.extract start (start + n)).size = n → start + n ≤ a.size := by
  simp +contextual +arith
  intro h
  omega

theorem canRead_mono {n m : Nat} (hn : n ≤ m) :
    SPred.entails (σs:=[File]) (canRead m) (canRead n) := by
  intro f
  simp[canRead]
  intro h
  omega

theorem serialized_canRead {s : Schema} (v : s.interp) (hn : n ≤ byteSize v):
    SPred.entails (σs:=[File]) (serialized v) (canRead n) := by
  apply SPred.entails.trans _ (canRead_mono hn)
  intro f
  simp [serialized, canRead]
  intro h
  simp[wp] at h
  split at h; case h_2 => contradiction
  rcases h with ⟨h₁, h₂⟩
  rw[← h₂] at h₁
  have := Array.extract_size_eq (Nat.le_of_lt_add_one f.pos.isLt) h₁
  simp_all

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

@[spec]
theorem read_spec :
  ⦃fun f' => ⌜canRead n f' ∧ f' = f⌝⦄
  FileM.read n
  ⦃⇓ v f' => hasRead v f f'⦄
  := by
  mintro h ∀f'
  mpure h
  have ⟨hread, hfile⟩ := h
  subst hfile
  unfold FileM.read
  mwp
  mspec (Specs.forIn'_list ?inv ?step)
  case inv => exact ⇓ (⟨pos, buf⟩, xs) =>
    ⌜pos = f'.pos + xs.pref.length ∧ pos + xs.suff.length ≤ f'.bytes.size
    ∧ f'.bytes.extract f'.pos pos = buf.toArray.take xs.pref.length⌝
  case pre => intro hread; simp_all[canRead]; omega
  case step =>
    intro ⟨pos, buf⟩ pref i hi suff hsuff
    have := range_elim hsuff
    simp at this
    subst_vars
    mintro ⌜hinv⌝
    simp at hinv
    mwp
    split
    · mpure_intro
      simp +arith [hinv]
      sorry -- pure proof about offset arithmetic and Array.extract
    · simp_all
      omega
  case post.except.handle => simp
  mintro ∀f
  simp_all [hasRead]

@[spec]
theorem read_spec' :
  ⦃fun f' => ⌜canRead n f' ∧ f' = f⌝⦄
  FileM.read n
  ⦃⇓ v f' => hasRead v f f'⦄
  := by
  mvcgen[-read_spec, FileM.read]

theorem serialized_hasRead_byte {bs : Vector UInt8 1} {v : Schema.byte.interp} :
    serialized v f → hasRead bs f f' → v = bs[0] := by
  simp[serialized, hasRead, Schema.serialize]
  wp_simp
  simp_all
  intro _ hv hbytes hpos hbs
  cases bs
  simp_all

example :
  ⦃fun f' => ⌜canRead n f' ∧ f' = f⌝⦄
  FileM.read n
  ⦃⇓ v f' => hasRead v f f'⦄
  = (
  (fun f' => ⌜canRead n f' ∧ f' = f⌝)
  ⊢ₛ
  wp⟦FileM.read n⟧ (⇓ v f' => hasRead v f f')
  )
  := rfl

example :
  wp⟦FileM.read n⟧ (⇓ v f' => hasRead v f f') f
  = (
  match FileM.read n f with
  | .ok v f' => hasRead v f f'
  | .error e f' => False
  )
  := rfl

example :
  PostCond α (.except FileError (.arg File .pure))
  = ((α → File → Prop) × (FileError → File → Prop) × Unit)
  := rfl

theorem serialized_hasRead_word {bs : Vector UInt8 4} {v : Schema.word.interp} :
    serialized v f → hasRead bs f f' → v = ((bs[0].toUInt32 <<< 24) ||| (bs[1].toUInt32 <<< 16) ||| (bs[2].toUInt32 <<< 8) ||| bs[3].toUInt32) := by
  simp[serialized, hasRead, Schema.serialize]
  wp_simp
  simp_all
  intro _ hv hbytes hpos hbs
  cases bs
  simp_all
  bv_decide

theorem serialized_hasRead_enum {alts : Fin nalts → Schema} {bs : Vector UInt8 1} {v : (alts tag).interp} :
    serialized v f → hasRead bs f f' → tag = bs[0] ∧ v = bs[1:] := by
  simp[serialized, hasRead, Schema.serialize]
  wp_simp
  simp_all
  intro _ hv hbytes hpos hbs
  cases bs
  simp_all

theorem blah {s : Schema} (v : s.interp) :
    ⦃serialized v⦄
    s.parse
    ⦃⇓ v' => ⌜v = v'⌝⦄ := by
  mintro hser
  induction s using Schema.parse.induct
  case case1 =>
    unfold Schema.parse
    mintro ∀f
    mpure hser
    mwp
    mspec read_spec
    case pre => mpure_intro; refine ⟨?_, rfl⟩; apply serialized_canRead _ .refl _ hser
    case post.success => intro f hread; exact serialized_hasRead_byte hser hread
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
