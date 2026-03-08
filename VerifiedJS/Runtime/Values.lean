/-
  VerifiedJS — Runtime Value Representation
  NaN-boxing in f64, or tagged pointers in i64.
-/

namespace VerifiedJS.Runtime

/-- NaN-boxed value representation.
    Uses the NaN payload bits of IEEE 754 f64 to tag different value types.
    - f64 values: any non-NaN f64 (or the canonical NaN)
    - Tagged values: NaN with specific bit patterns in the payload -/
structure NanBoxed where
  bits : UInt64
  deriving Repr, BEq

namespace NanBoxed

-- Tag constants for NaN-boxing
-- Quiet NaN mask: bit 51 set, exponent all 1s
def nanMask : UInt64 := 0x7FF8000000000000
-- Tag bits occupy bits 48-50
def tagMask : UInt64 := 0x0007000000000000
def payloadMask : UInt64 := 0x0000FFFFFFFFFFFF

def tagNull : UInt64 := 0x0001000000000000
def tagUndefined : UInt64 := 0x0002000000000000
def tagBool : UInt64 := 0x0003000000000000
def tagInt32 : UInt64 := 0x0004000000000000
def tagString : UInt64 := 0x0005000000000000
def tagObject : UInt64 := 0x0006000000000000
def tagSymbol : UInt64 := 0x0007000000000000

/-- Canonical numeric NaN used for JS `Number` NaN values (`ECMA-262 §6.1.6.1`). -/
def canonicalNaNBits : UInt64 := nanMask

/-- Runtime tags for non-number JS values (ECMA-262 §6.1). -/
inductive Tag where
  | null
  | undefined
  | bool
  | int32
  | string
  | object
  | symbol
  deriving Repr, BEq, DecidableEq

def tagToBits : Tag → UInt64
  | .null => tagNull
  | .undefined => tagUndefined
  | .bool => tagBool
  | .int32 => tagInt32
  | .string => tagString
  | .object => tagObject
  | .symbol => tagSymbol

def bitsToTag? : UInt64 → Option Tag
  | b =>
      if b == tagNull then
        some .null
      else if b == tagUndefined then
        some .undefined
      else if b == tagBool then
        some .bool
      else if b == tagInt32 then
        some .int32
      else if b == tagString then
        some .string
      else if b == tagObject then
        some .object
      else if b == tagSymbol then
        some .symbol
      else
        none

/-- Builds a boxed non-number value with a 48-bit payload. -/
def mkTagged (tag : Tag) (payload : UInt64) : NanBoxed :=
  { bits := nanMask ||| tagToBits tag ||| (payload &&& payloadMask) }

/-- A value is boxed if it is a quiet NaN payload with one of our runtime tags. -/
def isBoxed (v : NanBoxed) : Bool :=
  (v.bits &&& nanMask) == nanMask &&
    match bitsToTag? (v.bits &&& tagMask) with
    | some _ => true
    | none => false

def getTag? (v : NanBoxed) : Option Tag :=
  if (v.bits &&& nanMask) == nanMask then
    bitsToTag? (v.bits &&& tagMask)
  else
    none

def getPayload (v : NanBoxed) : UInt64 :=
  v.bits &&& payloadMask

/-- Numbers are carried as IEEE-754 bit patterns. All NaNs are canonicalized. -/
def encodeNumber (n : Float) : NanBoxed :=
  if n.isNaN then
    { bits := canonicalNaNBits }
  else
    { bits := Float.toBits n }

def encodeNull : NanBoxed :=
  mkTagged .null 0

def encodeUndefined : NanBoxed :=
  mkTagged .undefined 0

def encodeBool (b : Bool) : NanBoxed :=
  mkTagged .bool (if b then 1 else 0)

def encodeInt32 (i : Int32) : NanBoxed :=
  mkTagged .int32 i.toUInt32.toUInt64

/-- `sid` is a runtime string table identifier (ECMA-262 §6.1.4). -/
def encodeStringRef (sid : Nat) : NanBoxed :=
  mkTagged .string (UInt64.ofNat sid)

/-- `oid` is a runtime heap object identifier (ECMA-262 §6.1.7). -/
def encodeObjectRef (oid : Nat) : NanBoxed :=
  mkTagged .object (UInt64.ofNat oid)

def encodeSymbolRef (sid : Nat) : NanBoxed :=
  mkTagged .symbol (UInt64.ofNat sid)

/-- Decoded view of runtime values for interpreters and tests. -/
inductive Decoded where
  | number (n : Float)
  | null
  | undefined
  | bool (b : Bool)
  | int32 (i : Int32)
  | stringRef (sid : Nat)
  | objectRef (oid : Nat)
  | symbolRef (sid : Nat)
  deriving Repr, BEq

def decode (v : NanBoxed) : Decoded :=
  match getTag? v with
  | none => .number (Float.ofBits v.bits)
  | some .null => .null
  | some .undefined => .undefined
  | some .bool => .bool (getPayload v != 0)
  | some .int32 => .int32 (getPayload v).toUInt32.toInt32
  | some .string => .stringRef (getPayload v).toNat
  | some .object => .objectRef (getPayload v).toNat
  | some .symbol => .symbolRef (getPayload v).toNat

def decodeToNumber? (v : NanBoxed) : Option Float :=
  match decode v with
  | .number n => some n
  | _ => none

def decodeToBool? (v : NanBoxed) : Option Bool :=
  match decode v with
  | .bool b => some b
  | _ => none

def decodeToInt32? (v : NanBoxed) : Option Int32 :=
  match decode v with
  | .int32 i => some i
  | _ => none

/-! Sanity checks for the NaN-box encoding. -/
example : decode encodeNull = .null := rfl
example : decode encodeUndefined = .undefined := rfl
example : decode (encodeBool true) = .bool true := rfl
example : decode (encodeBool false) = .bool false := rfl
example : decode (encodeStringRef 42) = .stringRef 42 := rfl
example : decode (encodeObjectRef 7) = .objectRef 7 := rfl
example : decode (encodeSymbolRef 999) = .symbolRef 999 := rfl
example : decode (encodeInt32 (Int32.ofInt (-12345))) = .int32 (Int32.ofInt (-12345)) := rfl
example : decodeToNumber? encodeNull = none := rfl
example : decodeToBool? (encodeBool true) = some true := rfl
example : decodeToInt32? (encodeInt32 (Int32.ofInt (-1))) = some (Int32.ofInt (-1)) := rfl

end NanBoxed

end VerifiedJS.Runtime
