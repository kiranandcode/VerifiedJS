/-
  VerifiedJS — Wasm Execution Semantics
  Small-step reduction: store, stack, frames.
  SPEC: WebAssembly 1.0 §4.2, §4.4 (execution) and WasmCert-Coq `theories/operations.v`.
-/

import VerifiedJS.Wasm.Syntax
import VerifiedJS.Wasm.Numerics

namespace VerifiedJS.Wasm

/-- Runtime values used by the Wasm machine state. -/
inductive WasmValue where
  | i32 (n : UInt32)
  | i64 (n : UInt64)
  | f32 (n : Float)
  | f64 (n : Float)
  deriving Repr, BEq

/-- Observable execution events for Wasm small-step runs. -/
inductive TraceEvent where
  | silent
  | trap (msg : String)
  deriving Repr, BEq

/-- Wasm store (functions, tables, memories, globals). -/
structure Store where
  funcs : Array Func
  tables : Array (Array (Option Nat))
  memories : Array ByteArray
  globals : Array WasmValue
  deriving Repr

/-- Active call frame with locals and bound module instance id. -/
structure Frame where
  locals : Array WasmValue
  moduleInst : Nat
  deriving Repr

/-- Wasm execution state in evaluation context style. -/
structure ExecState where
  store : Store
  stack : List WasmValue
  frames : List Frame
  code : List Instr
  trace : List TraceEvent
  deriving Repr

/-- SPEC §4.4.3 Numeric Instructions: default value of a Wasm value type. -/
def defaultValue : ValType → WasmValue
  | .i32 => .i32 0
  | .i64 => .i64 0
  | .f32 => .f32 0.0
  | .f64 => .f64 0.0

/-- SPEC §4.5.3 Globals: initialize module globals with default typed values. -/
private def initGlobals (m : Module) : Array WasmValue :=
  m.globals.map (fun g => defaultValue g.type.val)

/-- SPEC §4.5.2 Tables: allocate table slots as `none` function references. -/
private def initTableSlots (tt : TableType) : Array (Option Nat) :=
  Array.replicate tt.lim.min none

/-- SPEC §4.5.5 Memories: allocate zero-initialized linear memories by pages. -/
private def initMemory (mt : MemType) : ByteArray :=
  let byteSize := mt.lim.min * 65536
  ByteArray.mk (Array.replicate byteSize 0)

/-- Build an initial store from a module declaration. -/
def initialStore (m : Module) : Store :=
  {
    funcs := m.funcs
    tables := m.tables.map initTableSlots
    memories := m.memories.map initMemory
    globals := initGlobals m
  }

/-- Initial machine state for a module entry; code starts at explicit start call if present. -/
def initialState (m : Module) : ExecState :=
  let entryCode :=
    match m.start with
    | some f => [Instr.call f]
    | none => []
  {
    store := initialStore m
    stack := []
    frames := [{ locals := #[], moduleInst := 0 }]
    code := entryCode
    trace := []
  }

private def pushTrace (s : ExecState) (t : TraceEvent) : ExecState :=
  { s with trace := s.trace ++ [t] }

private def trapState (s : ExecState) (msg : String) : TraceEvent × ExecState :=
  let s' := pushTrace { s with code := [] } (.trap msg)
  (.trap msg, s')

private def pop1? (stack : List WasmValue) : Option (WasmValue × List WasmValue) :=
  match stack with
  | v :: rest => some (v, rest)
  | [] => none

private def pop2? (stack : List WasmValue) : Option (WasmValue × WasmValue × List WasmValue) :=
  match stack with
  | v1 :: v2 :: rest => some (v1, v2, rest)
  | _ => none

private def pop3? (stack : List WasmValue) : Option (WasmValue × WasmValue × WasmValue × List WasmValue) :=
  match stack with
  | v1 :: v2 :: v3 :: rest => some (v1, v2, v3, rest)
  | _ => none

private def updateHeadFrame (frames : List Frame) (f : Frame) : List Frame :=
  match frames with
  | [] => [f]
  | _ :: rest => f :: rest

private def i32Truth : WasmValue → Option Bool
  | .i32 n => some (n != 0)
  | _ => none

private def withI32Bin
    (s : ExecState)
    (op : UInt32 → UInt32 → UInt32)
    (name : String) : Option (TraceEvent × ExecState) :=
  match pop2? s.stack with
  | some (.i32 rhs, .i32 lhs, rest) =>
      let v := WasmValue.i32 (op lhs rhs)
      some (.silent, pushTrace { s with stack := v :: rest } .silent)
  | _ => some (trapState s s!"type mismatch in {name}")

private def withI64Bin
    (s : ExecState)
    (op : UInt64 → UInt64 → UInt64)
    (name : String) : Option (TraceEvent × ExecState) :=
  match pop2? s.stack with
  | some (.i64 rhs, .i64 lhs, rest) =>
      let v := WasmValue.i64 (op lhs rhs)
      some (.silent, pushTrace { s with stack := v :: rest } .silent)
  | _ => some (trapState s s!"type mismatch in {name}")

private def withF64Bin
    (s : ExecState)
    (op : Float → Float → Float)
    (name : String) : Option (TraceEvent × ExecState) :=
  match pop2? s.stack with
  | some (.f64 rhs, .f64 lhs, rest) =>
      let v := WasmValue.f64 (op lhs rhs)
      some (.silent, pushTrace { s with stack := v :: rest } .silent)
  | _ => some (trapState s s!"type mismatch in {name}")

/-- One deterministic Wasm machine step (administrative reduction function). -/
def step? (s : ExecState) : Option (TraceEvent × ExecState) :=
  match s.code with
  | [] => none
  | i :: rest =>
      let base := { s with code := rest }
      match i with
      | .unreachable => some (trapState base "unreachable executed")
      | .nop => some (.silent, pushTrace base .silent)
      | .block _ body =>
          let s' := pushTrace { base with code := body ++ rest } .silent
          some (.silent, s')
      | .loop _ body =>
          -- Structured loops are represented directly; branch semantics is refined later.
          let s' := pushTrace { base with code := body ++ rest } .silent
          some (.silent, s')
      | .if_ _ then_ else_ =>
          match pop1? base.stack with
          | some (cond, stk) =>
              match i32Truth cond with
              | some true =>
                  some (.silent, pushTrace { base with stack := stk, code := then_ ++ rest } .silent)
              | some false =>
                  some (.silent, pushTrace { base with stack := stk, code := else_ ++ rest } .silent)
              | none => some (trapState base "if condition is not i32")
          | none => some (trapState base "stack underflow in if")
      | .br _ =>
          some (.silent, pushTrace { base with code := [] } .silent)
      | .brIf _ =>
          match pop1? base.stack with
          | some (cond, stk) =>
              match i32Truth cond with
              | some true => some (.silent, pushTrace { base with stack := stk, code := [] } .silent)
              | some false => some (.silent, pushTrace { base with stack := stk } .silent)
              | none => some (trapState base "br_if condition is not i32")
          | none => some (trapState base "stack underflow in br_if")
      | .brTable _ _ =>
          match pop1? base.stack with
          | some (cond, stk) =>
              match cond with
              | .i32 _ => some (.silent, pushTrace { base with stack := stk, code := [] } .silent)
              | _ => some (trapState base "br_table index is not i32")
          | none => some (trapState base "stack underflow in br_table")
      | .return_ =>
          let s' := pushTrace { base with code := [] } .silent
          some (.silent, s')
      | .call idx =>
          if h : idx < base.store.funcs.size then
            let func := base.store.funcs[idx]
            let locals := (func.locals.map defaultValue).toArray
            let frame : Frame := { locals := locals, moduleInst := 0 }
            let s' := pushTrace { base with frames := frame :: base.frames, code := func.body ++ rest } .silent
            some (.silent, s')
          else
            some (trapState base s!"unknown function index {idx}")
      | .callIndirect _ tableIdx =>
          match pop1? base.stack with
          | some (.i32 elemIdx, stk) =>
              if hTbl : tableIdx < base.store.tables.size then
                let table := base.store.tables[tableIdx]
                if hElem : elemIdx.toNat < table.size then
                  match table[elemIdx.toNat] with
                  | some funcIdx =>
                      if hFunc : funcIdx < base.store.funcs.size then
                        let func := base.store.funcs[funcIdx]
                        let locals := (func.locals.map defaultValue).toArray
                        let frame : Frame := { locals := locals, moduleInst := 0 }
                        let s' := pushTrace
                          { base with stack := stk, frames := frame :: base.frames, code := func.body ++ rest } .silent
                        some (.silent, s')
                      else
                        some (trapState base s!"unknown function index {funcIdx}")
                  | none => some (trapState base s!"uninitialized table slot {elemIdx.toNat}")
                else
                  some (trapState base s!"table index out of bounds {elemIdx.toNat}")
              else
                some (trapState base s!"unknown table index {tableIdx}")
          | some (_, _) => some (trapState base "call_indirect element index is not i32")
          | none => some (trapState base "stack underflow in call_indirect")
      | .drop =>
          match pop1? base.stack with
          | some (_, stk) => some (.silent, pushTrace { base with stack := stk } .silent)
          | none => some (trapState base "stack underflow in drop")
      | .select =>
          match pop2? base.stack with
          | some (cond, v2, tail) =>
              match pop1? tail with
              | some (v1, restStack) =>
                  match i32Truth cond with
                  | some true => some (.silent, pushTrace { base with stack := v1 :: restStack } .silent)
                  | some false => some (.silent, pushTrace { base with stack := v2 :: restStack } .silent)
                  | none => some (trapState base "select condition is not i32")
              | none => some (trapState base "stack underflow in select")
          | none => some (trapState base "stack underflow in select")
      | .localGet idx =>
          match base.frames with
          | fr :: _ =>
              if h : idx < fr.locals.size then
                let v := fr.locals[idx]
                some (.silent, pushTrace { base with stack := v :: base.stack } .silent)
              else
                some (trapState base s!"unknown local index {idx}")
          | [] => some (trapState base "local.get without active frame")
      | .localSet idx =>
          match base.frames, pop1? base.stack with
          | fr :: _, some (v, stk) =>
              if h : idx < fr.locals.size then
                let fr' := { fr with locals := fr.locals.set! idx v }
                let s' := pushTrace
                  { base with stack := stk, frames := updateHeadFrame base.frames fr' } .silent
                some (.silent, s')
              else
                some (trapState base s!"unknown local index {idx}")
          | [], _ => some (trapState base "local.set without active frame")
          | _, none => some (trapState base "stack underflow in local.set")
      | .localTee idx =>
          match base.frames, pop1? base.stack with
          | fr :: _, some (v, stk) =>
              if h : idx < fr.locals.size then
                let fr' := { fr with locals := fr.locals.set! idx v }
                let s' := pushTrace
                  { base with stack := v :: stk, frames := updateHeadFrame base.frames fr' } .silent
                some (.silent, s')
              else
                some (trapState base s!"unknown local index {idx}")
          | [], _ => some (trapState base "local.tee without active frame")
          | _, none => some (trapState base "stack underflow in local.tee")
      | .globalGet idx =>
          if h : idx < base.store.globals.size then
            let v := base.store.globals[idx]
            some (.silent, pushTrace { base with stack := v :: base.stack } .silent)
          else
            some (trapState base s!"unknown global index {idx}")
      | .globalSet idx =>
          match pop1? base.stack with
          | some (v, stk) =>
              if h : idx < base.store.globals.size then
                let globals' := base.store.globals.set! idx v
                let store' := { base.store with globals := globals' }
                some (.silent, pushTrace { base with stack := stk, store := store' } .silent)
              else
                some (trapState base s!"unknown global index {idx}")
          | none => some (trapState base "stack underflow in global.set")
      | .i32Const n =>
          some (.silent, pushTrace { base with stack := WasmValue.i32 n :: base.stack } .silent)
      | .i64Const n =>
          some (.silent, pushTrace { base with stack := WasmValue.i64 n :: base.stack } .silent)
      | .f32Const n =>
          some (.silent, pushTrace { base with stack := WasmValue.f32 n :: base.stack } .silent)
      | .f64Const n =>
          some (.silent, pushTrace { base with stack := WasmValue.f64 n :: base.stack } .silent)
      | .i32Add => withI32Bin base Numerics.i32Add "i32.add"
      | .i32Sub => withI32Bin base Numerics.i32Sub "i32.sub"
      | .i32Mul => withI32Bin base Numerics.i32Mul "i32.mul"
      | .i64Add => withI64Bin base Numerics.i64Add "i64.add"
      | .i64Sub => withI64Bin base Numerics.i64Sub "i64.sub"
      | .i64Mul => withI64Bin base Numerics.i64Mul "i64.mul"
      | .f64Add => withF64Bin base Numerics.f64Add "f64.add"
      | .f64Sub => withF64Bin base Numerics.f64Sub "f64.sub"
      | .f64Mul => withF64Bin base Numerics.f64Mul "f64.mul"
      | .f64Div => withF64Bin base Numerics.f64Div "f64.div"
      | .memorySize memIdx =>
          if hMem : memIdx < base.store.memories.size then
            let mem := base.store.memories[memIdx]
            let pages := UInt32.ofNat (mem.size / 65536)
            some (.silent, pushTrace { base with stack := .i32 pages :: base.stack } .silent)
          else
            some (trapState base s!"unknown memory index {memIdx}")
      | .memoryGrow memIdx =>
          match pop1? base.stack with
          | some (.i32 delta, stk) =>
              if hMem : memIdx < base.store.memories.size then
                let mem := base.store.memories[memIdx]
                let oldPages := mem.size / 65536
                let grown := ByteArray.mk (mem.toList.toArray ++ Array.replicate (delta.toNat * 65536) 0)
                let store' := { base.store with memories := base.store.memories.set! memIdx grown }
                some (.silent, pushTrace { base with store := store', stack := .i32 (UInt32.ofNat oldPages) :: stk } .silent)
              else
                some (trapState base s!"unknown memory index {memIdx}")
          | some (_, _) => some (trapState base "memory.grow delta is not i32")
          | none => some (trapState base "stack underflow in memory.grow")
      | .i32Load _ | .i64Load _ | .f32Load _ | .f64Load _
      | .i32Load8s _ | .i32Load8u _ | .i32Load16s _ | .i32Load16u _
      | .i64Load8s _ | .i64Load8u _ | .i64Load16s _ | .i64Load16u _
      | .i64Load32s _ | .i64Load32u _
      | .i32Store _ | .i64Store _ | .f32Store _ | .f64Store _
      | .i32Store8 _ | .i32Store16 _ | .i64Store8 _ | .i64Store16 _ | .i64Store32 _
      | .i32Eqz | .i32Eq | .i32Ne | .i32Lts | .i32Ltu | .i32Gts | .i32Gtu | .i32Les | .i32Leu
      | .i32Ges | .i32Geu | .i32Clz | .i32Ctz | .i32Popcnt | .i32DivS | .i32DivU | .i32RemS
      | .i32RemU | .i32And | .i32Or | .i32Xor | .i32Shl | .i32ShrS | .i32ShrU | .i32Rotl | .i32Rotr
      | .i64Eqz | .i64Eq | .i64Ne | .i64Lts | .i64Ltu | .i64Gts | .i64Gtu | .i64Les | .i64Leu
      | .i64Ges | .i64Geu | .i64Clz | .i64Ctz | .i64Popcnt | .i64DivS | .i64DivU | .i64RemS
      | .i64RemU | .i64And | .i64Or | .i64Xor | .i64Shl | .i64ShrS | .i64ShrU | .i64Rotl | .i64Rotr
      | .f32Eq | .f32Ne | .f32Lt | .f32Gt | .f32Le | .f32Ge | .f32Abs | .f32Neg | .f32Ceil
      | .f32Floor | .f32Trunc | .f32Nearest | .f32Sqrt | .f32Add | .f32Sub | .f32Mul | .f32Div
      | .f32Min | .f32Max | .f32Copysign
      | .f64Eq | .f64Ne | .f64Lt | .f64Gt | .f64Le | .f64Ge | .f64Abs | .f64Neg | .f64Ceil
      | .f64Floor | .f64Trunc | .f64Nearest | .f64Sqrt | .f64Min | .f64Max | .f64Copysign
      | .i32WrapI64 | .i32TruncF32s | .i32TruncF32u | .i32TruncF64s | .i32TruncF64u
      | .i64ExtendI32s | .i64ExtendI32u | .i64TruncF32s | .i64TruncF32u | .i64TruncF64s
      | .i64TruncF64u | .f32ConvertI32s | .f32ConvertI32u | .f32ConvertI64s | .f32ConvertI64u
      | .f32DemoteF64 | .f64ConvertI32s | .f64ConvertI32u | .f64ConvertI64s | .f64ConvertI64u
      | .f64PromoteF32 | .i32ReinterpretF32 | .f32ReinterpretI32 | .i64ReinterpretF64
      | .f64ReinterpretI64 =>
          match pop1? base.stack with
          | some (.i64 n, stk) =>
              some (.silent, pushTrace { base with stack := .f64 (Float.ofNat n.toNat) :: stk } .silent)
          | some (_, _) => some (trapState base "type mismatch in f64.reinterpret_i64")
          | none => some (trapState base "stack underflow in f64.reinterpret_i64")
      | .memoryInit _ _ | .dataDrop _ | .memoryCopy _ _ | .memoryFill _
      | .tableInit _ _ | .elemDrop _ | .tableCopy _ _ =>
          match pop3? base.stack with
          | some (.i32 _, .i32 _, .i32 _, stk) =>
              some (.silent, pushTrace { base with stack := stk } .silent)
          | _ => some (trapState base s!"unsupported bulk operation in current executable model: {repr i}")

/-- Small-step reduction relation induced by `step?`. -/
inductive Step : ExecState → TraceEvent → ExecState → Prop where
  | mk {s : ExecState} {t : TraceEvent} {s' : ExecState} :
      step? s = some (t, s') →
      Step s t s'

/-- Reflexive-transitive closure of Wasm machine steps with trace accumulation. -/
inductive Steps : ExecState → List TraceEvent → ExecState → Prop where
  | refl (s : ExecState) : Steps s [] s
  | tail {s1 s2 s3 : ExecState} {t : TraceEvent} {ts : List TraceEvent} :
      Step s1 t s2 →
      Steps s2 ts s3 →
      Steps s1 (t :: ts) s3

/-- Behavioral semantics for a Wasm module run from `initialState`. -/
def Behaves (m : Module) (b : List TraceEvent) : Prop :=
  ∃ s', Steps (initialState m) b s' ∧ step? s' = none

end VerifiedJS.Wasm
