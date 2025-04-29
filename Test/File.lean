import MPL

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
  modify fun f => { bytes := f.bytes ++ bytes, pos := f.pos.castLE (by simp[f.pos.isLt]) }

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
  | struct (nflds : Nat) (flds : Fin nflds → Schema)
  | array (elt : Schema)

def Pi.toTuple (n : Nat) (f : Fin n → Type) : Type := match n with
  | 0 => PUnit
  | n + 1 => f 0 × Pi.toTuple n (f ∘ Fin.succ)

abbrev Schema.interp (s : Schema) : Type := match s with
  | byte => UInt8
  | word => UInt32
  | enum nalts _ alts => Σ i : Fin nalts, (alts i).interp
  | struct nflds flds => Pi.toTuple nflds (fun i => (flds i).interp)
  | array elt => Array (Schema.interp elt)

def Schema.parse (s : Schema) : FileM s.interp := do
  match s with
  | byte => do
    let b ← FileM.read 1
    return b[0]
  | word => do
    let bs ← FileM.read 4
    let mut ret : UInt32 := 0
    for b in bs do
      ret := ret <<< 8 + b.toUInt32
    return ret
  | enum nalts _ alts => do
    let i ← FileM.read 1
    let tag := i[0]
    if h : tag.toNat < nalts
    then
      let tag := ⟨tag.toNat, h⟩
      return ⟨tag, ← (alts tag).parse⟩
    else throw FileError.invalidFormat
  | struct nflds flds => do
    match h : nflds with
    | 0 => return ()
    | nflds + 1 => do
      let hd ← (flds 0).parse
      let tl ← (struct nflds (flds ∘ Fin.succ)).parse
      return (hd, tl)
  | array elt => do
    let n ← FileM.read 1
    let n := n[0].toNat
    let mut ret := Array.mkEmpty n
    for i in [:n] do
      ret := ret.push (← elt.parse)
    return ret
decreasing_by (repeat sorry)

def Schema.serialize (s : Schema) (v : s.interp) : FileM PUnit := do
  match s, v with
  | byte, b => do
    FileM.append #[b]
  | word, w => do
    FileM.append (#[w >>> 24, w >>> 16, w >>> 8, w].map (·.toUInt8))
  | enum nalts h alts, ⟨tag, v⟩ => do
    FileM.append #[.ofBitVec (tag.castLE h)]
    (alts tag).serialize v
  | struct nflds flds, t => do
    match h : nflds with
    | 0 => return ()
    | nflds + 1 => do
      (flds 0).serialize (t.fst)
      (struct nflds (flds ∘ Fin.succ)).serialize t.snd
  | array elt, a => do
    FileM.append #[a.size.toUInt8]
    for (v : elt.interp) in (a : Array elt.interp) do
      elt.serialize v
decreasing_by (repeat sorry)

--derive_wp_simp FileM.append
@[wp_simp]
theorem FileM.append_apply :
    wp⟦FileM.append bs⟧.apply Q = fun f => Q.1 ⟨⟩ { f with bytes := f.bytes ++ bs, pos := f.pos.castLE (by simp) } := by
  unfold FileM.append
  mstart
  mwp

theorem FileM.append_ok : ⦃⌜True⌝⦄ FileM.append bs ⦃⇓ () => ⌜True⌝⦄ := by
  mintro - ∀s
  mwp

theorem Schema.serialize_ok {s : Schema} (v : s.interp) :
  ⦃⌜True⌝⦄ s.serialize v ⦃⇓ () => ⌜True⌝⦄ := by
  induction s, v using Schema.serialize.induct
  case case1 => unfold Schema.serialize; mintro - ∀f; mwp
  case case2 => unfold Schema.serialize; mintro - ∀f; mwp
  case case3 ih => unfold Schema.serialize; mintro - ∀f; mwp; mspec ih
  case case4 ih => unfold Schema.serialize; mintro - ∀f; mwp
  case case5 ih1 ih2 => unfold Schema.serialize; mintro - ∀f; mwp; mspec ih1; mspec ih2
  case case6 arr ih =>
    unfold Schema.serialize
    mintro - ∀f
    mwp
    cases arr
    conv in wp _ => simp
    mspec (Specs.foldlM_list (m := FileM) (⇓ _ => ⌜True⌝) ?step)
    case step => intros; apply ih

def Schema.fileSize {s : Schema} (v : s.interp) : Nat :=
  match EStateM.run (s.serialize v) File.mkEmpty with
  | .ok _ f => f.bytes.size
  | .error _ _ => panic! "failed to serialize"

theorem Triple.conj [WP m ps] (x : m α) (h₁ : ⦃P₁⦄ x ⦃Q₁⦄) (h₂ : ⦃P₂⦄ x ⦃Q₂⦄) : ⦃P₁ ∧ P₂⦄ x ⦃Q₁ ∧ₚ Q₂⦄ := by
  mintro ⟨hp₁, hp₂⟩ ∀s
  mreplace hp₁ := h₁ hp₁
  h₁ hp₁
  mwp
  mspec h₁
  mspec h₂

def Schema.wellFormedSubFile (s : Schema) (f : File) : Prop :=
  ∃ v : s.interp, match EStateM.run (s.serialize v) File.mkEmpty with
  | .ok () f0 => f.bytes[f.pos.val : f.pos.val + f0.bytes.size] = f0.bytes
  | .error _ _ => False
def Schema.wellFormedSubFile2 (s : Schema) (f : File) : Prop :=
  ∃ v : s.interp, (s.serialize v) File.mkEmpty with
  | .ok () f0 => f.bytes[f.pos.val : f.pos.val + f0.bytes.size] = f0.bytes
  | .error _ _ => False
