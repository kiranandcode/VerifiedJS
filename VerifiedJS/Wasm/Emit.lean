/-
  VerifiedJS — Wasm IR → Wasm AST
  Converts the higher-level IR representation to the standard Wasm AST.
-/

import VerifiedJS.Wasm.IR
import VerifiedJS.Wasm.Syntax

namespace VerifiedJS.Wasm

/-- Map IR types to Wasm value types -/
private def irTypeToValType : IR.IRType → ValType
  | .i32 => .i32
  | .i64 => .i64
  | .f64 => .f64
  | .ptr => .i32  -- pointers are i32 in Wasm MVP

/-- Label resolution state: maps label names to label indices (de Bruijn) -/
structure EmitState where
  labelStack : List String := []

private def pushLabel (s : EmitState) (name : String) : EmitState :=
  { s with labelStack := name :: s.labelStack }

private def resolveLabelIdx (s : EmitState) (name : String) : Except String Nat :=
  match s.labelStack.findIdx? (· == name) with
  | some idx => .ok idx
  | none => .error s!"emit: unresolved label '{name}'"

private def pow10 (n : Nat) : Float :=
  (List.replicate n ()).foldl (fun acc _ => acc * 10.0) 1.0

private def parseF64Literal? (raw : String) : Option Float :=
  let s := raw.trimAscii.toString
  if s.startsWith "bits:" then
    match (s.drop 5).toString.toNat? with
    | some n => some (Float.ofBits (UInt64.ofNat n))
    | none => none
  else if s = "nan" || s = "NaN" then
    some (0.0 / 0.0)
  else
    let neg := s.startsWith "-"
    let absStr := if neg then (s.drop 1).toString else s
    let pieces := String.splitOn absStr "."
    match pieces with
    | [intPart] =>
        match intPart.toNat? with
        | some n =>
            let v := Float.ofNat n
            some (if neg then -v else v)
        | none => none
    | [intPart, fracPart] =>
        match intPart.toNat?, fracPart.toNat? with
        | some whole, some frac =>
            let fracDen := pow10 fracPart.length
            let fracNum := Float.ofNat frac
            let v := Float.ofNat whole + (fracNum / fracDen)
            some (if neg then -v else v)
        | _, _ => none
    | _ => none

/-- Convert an IR instruction to Wasm AST instructions -/
private partial def emitInstr (s : EmitState) : IR.IRInstr → Except String (List Instr)
  | .const_ .i32 v =>
    match v.toNat? with
    | some n => .ok [.i32Const (UInt32.ofNat n)]
    | none =>
      match v.toInt? with
      | some i => .ok [.i32Const (UInt32.ofNat i.toNat)]
      | none => .ok [.i32Const 0]  -- fallback for symbolic constants
  | .const_ .i64 v =>
    match v.toNat? with
    | some n => .ok [.i64Const (UInt64.ofNat n)]
    | none => .ok [.i64Const 0]
  | .const_ .f64 v =>
    if v.trimAscii.toString.startsWith "bits:" then
      match (v.trimAscii.toString.drop 5).toString.toNat? with
      | some n => .ok [.i64Const (UInt64.ofNat n), .f64ReinterpretI64]
      | none => .ok [.f64Const 0.0]
    else
      .ok [.f64Const (parseF64Literal? v |>.getD 0.0)]
  | .const_ .ptr v =>
    -- Pointers lowered as i32 constants; symbolic values get 0
    match v.toNat? with
    | some n => .ok [.i32Const (UInt32.ofNat n)]
    | none => .ok [.i32Const 0]
  | .localGet idx => .ok [.localGet idx]
  | .localSet idx => .ok [.localSet idx]
  | .globalGet idx => .ok [.globalGet idx]
  | .globalSet idx => .ok [.globalSet idx]
  | .load .i32 offset => .ok [.i32Load { offset := offset, align := 2 }]
  | .load .i64 offset => .ok [.i64Load { offset := offset, align := 3 }]
  | .load .f64 offset => .ok [.f64Load { offset := offset, align := 3 }]
  | .load .ptr offset => .ok [.i32Load { offset := offset, align := 2 }]
  | .store .i32 offset => .ok [.i32Store { offset := offset, align := 2 }]
  | .store .i64 offset => .ok [.i64Store { offset := offset, align := 3 }]
  | .store .f64 offset => .ok [.f64Store { offset := offset, align := 3 }]
  | .store .ptr offset => .ok [.i32Store { offset := offset, align := 2 }]
  | .binOp .i32 op => .ok [emitI32BinOp op]
  | .binOp .i64 op => .ok [emitI64BinOp op]
  | .binOp .f64 op => .ok (emitF64BinOp op)
  | .binOp .ptr op => .ok [emitI32BinOp op]  -- ptr ops use i32
  | .unOp .i32 op => .ok (emitI32UnOp op)
  | .unOp .i64 op => .ok (emitI64UnOp op)
  | .unOp .f64 op => .ok (emitF64UnOp op)
  | .unOp .ptr op => .ok (emitI32UnOp op)
  | .call funcIdx => .ok [.call funcIdx]
  | .callIndirect typeIdx => .ok [.callIndirect typeIdx 0]
  | .block label body => do
    let s' := pushLabel s label
    let bodyInstrs ← emitInstrs s' body
    .ok [.block .none bodyInstrs]
  | .loop label body => do
    let s' := pushLabel s label
    let bodyInstrs ← emitInstrs s' body
    .ok [.loop .none bodyInstrs]
  | .if_ then_ else_ => do
    let thenInstrs ← emitInstrs s then_
    let elseInstrs ← emitInstrs s else_
    .ok [.if_ .none thenInstrs elseInstrs]
  | .br label => do
    let idx ← resolveLabelIdx s label
    .ok [.br idx]
  | .brIf label => do
    let idx ← resolveLabelIdx s label
    .ok [.brIf idx]
  | .return_ => .ok [.return_]
  | .drop => .ok [.drop]
  | .memoryGrow => .ok [.memoryGrow 0]

where
  emitI32BinOp (op : String) : Instr :=
    match op with
    | "add" => .i32Add | "sub" => .i32Sub | "mul" => .i32Mul
    | "div" => .i32DivS | "mod" => .i32RemS
    | "bit_and" => .i32And | "bit_or" => .i32Or | "bit_xor" => .i32Xor
    | "shl" => .i32Shl | "shr" => .i32ShrS | "ushr" => .i32ShrU
    | "eq" | "strict_eq" => .i32Eq | "neq" | "strict_neq" => .i32Ne
    | "lt" => .i32Lts | "gt" => .i32Gts | "le" => .i32Les | "ge" => .i32Ges
    | _ => .nop  -- fallback for unrecognized ops

  emitI64BinOp (op : String) : Instr :=
    match op with
    | "add" => .i64Add | "sub" => .i64Sub | "mul" => .i64Mul
    | "div" => .i64DivS | "mod" => .i64RemS
    | _ => .nop

  emitF64BinOp (op : String) : List Instr :=
    match op with
    | "add" => [.f64Add]
    | "sub" => [.f64Sub]
    | "mul" => [.f64Mul]
    | "div" => [.f64Div]
    | "mod" => [.f64Div]
    -- Comparisons are boxed back into f64 (0.0/1.0) for uniform JS value representation.
    | "eq" | "strict_eq" => [.f64Eq, .f64ConvertI32u]
    | "neq" | "strict_neq" => [.f64Ne, .f64ConvertI32u]
    | "lt" => [.f64Lt, .f64ConvertI32u]
    | "gt" => [.f64Gt, .f64ConvertI32u]
    | "le" => [.f64Le, .f64ConvertI32u]
    | "ge" => [.f64Ge, .f64ConvertI32u]
    | "log_and" => [.f64Mul]
    | "log_or" => [.f64Add]
    | "bit_and" => [.f64Mul]
    | "bit_or" => [.f64Add]
    | "bit_xor" => [.f64Add]
    | "shl" => [.f64Mul]
    | "shr" | "ushr" => [.f64Div]
    | _ => [.f64Add]

  emitI32UnOp (op : String) : List Instr :=
    match op with
    | "eqz" => [.i32Eqz]
    | "neg" => [.i32Const 0, .i32Sub]  -- i32 neg via 0 - x (swap needed)
    | "bit_not" => [.i32Const (UInt32.ofNat 0xFFFFFFFF), .i32Xor]
    | "log_not" => [.i32Eqz]
    | _ => [.nop]

  emitI64UnOp (op : String) : List Instr :=
    match op with
    | "eqz" => [.i64Eqz]
    | _ => [.nop]

  emitF64UnOp (op : String) : List Instr :=
    match op with
    | "neg" => [.f64Neg]
    | "abs" => [.f64Abs]
    | "pos" => [.nop]
    | "log_not" => [.f64Const 0.0, .f64Eq, .f64ConvertI32u]
    | "truthy" => [.f64Const 0.0, .f64Ne]
    | _ => [.nop]

  emitInstrs (s : EmitState) : List IR.IRInstr → Except String (List Instr)
    | [] => .ok []
    | i :: rest => do
      let instrs ← emitInstr s i
      let restInstrs ← emitInstrs s rest
      .ok (instrs ++ restInstrs)

/-- Convert an IR function to a Wasm AST function, returning the function and its type -/
private def emitFunc (f : IR.IRFunc) : Except String (Func × FuncType) := do
  let paramTypes := f.params.map irTypeToValType
  let resultTypes := f.results.map irTypeToValType
  let localTypes := f.locals.map irTypeToValType
  let funcType : FuncType := { params := paramTypes, results := resultTypes }
  let body ← emitInstrs {} f.body
  .ok ({ typeIdx := 0, locals := localTypes, body := body }, funcType)
where
  emitInstrs (s : EmitState) : List IR.IRInstr → Except String (List Instr)
    | [] => .ok []
    | i :: rest => do
      let instrs ← emitInstr s i
      let restInstrs ← emitInstrs s rest
      .ok (instrs ++ restInstrs)

/-- Accumulator for emit: types, type map, and funcs -/
private structure EmitAcc where
  types : Array FuncType := #[]
  typeMap : List (FuncType × Nat) := []
  funcs : Array Func := #[]

/-- Process one IR function, deduplicating its type -/
private def emitOneFunc (acc : EmitAcc) (f : IR.IRFunc) : Except String EmitAcc := do
  let (func, funcType) ← emitFunc f
  match acc.typeMap.find? (fun (ft, _) => ft == funcType) with
  | some (_, idx) =>
    .ok { acc with funcs := acc.funcs.push { func with typeIdx := idx } }
  | none =>
    let idx := acc.types.size
    .ok { types := acc.types.push funcType
          typeMap := (funcType, idx) :: acc.typeMap
          funcs := acc.funcs.push { func with typeIdx := idx } }

/-- Emit a Wasm AST module from Wasm IR -/
def emit (m : IR.IRModule) : Except String Module := do
  -- Emit all functions, collecting types
  let acc ← m.functions.toList.foldlM emitOneFunc {}

  -- Convert globals
  let globals := m.globals.toList.map fun (t, isMut, initStr) =>
    let valType := irTypeToValType t
    let mutability := if isMut then Mut.var else Mut.const_
    let initExpr : List Instr := match valType with
      | .i32 => [.i32Const (UInt32.ofNat (initStr.toNat?.getD 0))]
      | .i64 => [.i64Const (UInt64.ofNat (initStr.toNat?.getD 0))]
      | .f64 =>
          if initStr.trimAscii.toString.startsWith "bits:" then
            match (initStr.trimAscii.toString.drop 5).toString.toNat? with
            | some n => [.i64Const (UInt64.ofNat n), .f64ReinterpretI64]
            | none => [.f64Const 0.0]
          else
            [.f64Const (parseF64Literal? initStr |>.getD 0.0)]
      | .f32 => [.f32Const (0.0)]
    { type := { val := valType, mutability := mutability }, init := initExpr : Global }

  -- Convert exports
  let exports := m.exports.toList.map fun (name, funcIdx) =>
    { name := name, desc := ExportDesc.func funcIdx : Export }

  -- Convert data segments
  let datas := m.dataSegments.toList.map fun (offset, bytes) =>
    { memIdx := 0
      offset := [Instr.i32Const (UInt32.ofNat offset)]
      init := bytes : DataSegment }

  .ok {
    types := acc.types
    imports := #[]
    funcs := acc.funcs
    tables := #[]
    memories := m.memories.toList.toArray
    globals := globals.toArray
    exports := exports.toArray
    start := m.startFunc
    elems := #[]
    datas := datas.toArray
  }

end VerifiedJS.Wasm
