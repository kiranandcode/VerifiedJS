/-
  VerifiedJS — Lowering: JS.ANF → Wasm.IR
-/

import VerifiedJS.ANF.Syntax
import VerifiedJS.Wasm.IR

namespace VerifiedJS.Wasm

open Std

abbrev RuntimeFuncIdx := Nat

-- Runtime helper dispatch table used by lowering.
-- These helpers model ECMA-262 runtime operations (e.g. property access and calls; §13, §7.3).
namespace RuntimeIdx

def call : RuntimeFuncIdx := 0
def construct : RuntimeFuncIdx := 1
def getProp : RuntimeFuncIdx := 2
def setProp : RuntimeFuncIdx := 3
def getIndex : RuntimeFuncIdx := 4
def setIndex : RuntimeFuncIdx := 5
def deleteProp : RuntimeFuncIdx := 6
def typeofOp : RuntimeFuncIdx := 7
def getEnv : RuntimeFuncIdx := 8
def makeEnv : RuntimeFuncIdx := 9
def makeClosure : RuntimeFuncIdx := 10
def objectLit : RuntimeFuncIdx := 11
def arrayLit : RuntimeFuncIdx := 12
def throwOp : RuntimeFuncIdx := 13
def yieldOp : RuntimeFuncIdx := 14
def awaitOp : RuntimeFuncIdx := 15

end RuntimeIdx

structure LowerCtx where
  locals : List (ANF.VarName × Nat)
  deriving Inhabited

structure LowerState where
  nextLocal : Nat
  locals : Array IR.IRType
  deriving Inhabited

abbrev LowerM := StateT LowerState (Except String)

private def lookupLocal (ctx : LowerCtx) (name : ANF.VarName) : Except String Nat :=
  match ctx.locals.find? (fun pair => pair.fst = name) with
  | some (_, idx) => .ok idx
  | none => .error s!"lower: unbound variable '{name}'"

private def allocLocal (name : ANF.VarName) (ctx : LowerCtx) : LowerM (Nat × LowerCtx) := do
  let st ← get
  let idx := st.nextLocal
  set { st with nextLocal := idx + 1, locals := st.locals.push .ptr }
  pure (idx, { ctx with locals := (name, idx) :: ctx.locals })

private def lowerUnaryOp : Core.UnaryOp → String
  | .neg => "neg"
  | .pos => "pos"
  | .bitNot => "bit_not"
  | .logNot => "log_not"
  | .void => "void"

private def lowerBinOp : Core.BinOp → String
  | .add => "add"
  | .sub => "sub"
  | .mul => "mul"
  | .div => "div"
  | .mod => "mod"
  | .exp => "exp"
  | .eq => "eq"
  | .neq => "neq"
  | .strictEq => "strict_eq"
  | .strictNeq => "strict_neq"
  | .lt => "lt"
  | .gt => "gt"
  | .le => "le"
  | .ge => "ge"
  | .bitAnd => "bit_and"
  | .bitOr => "bit_or"
  | .bitXor => "bit_xor"
  | .shl => "shl"
  | .shr => "shr"
  | .ushr => "ushr"
  | .logAnd => "log_and"
  | .logOr => "log_or"
  | .instanceof => "instanceof"
  | .in => "in"

private def boolAsI32 (b : Bool) : String :=
  if b then "1" else "0"

private def lowerTrivial (ctx : LowerCtx) : ANF.Trivial → Except String (List IR.IRInstr)
  | .var name => do
      let idx ← lookupLocal ctx name
      pure [IR.IRInstr.localGet idx]
  | .litNull => pure [IR.IRInstr.const_ .ptr "null"]
  | .litUndefined => pure [IR.IRInstr.const_ .ptr "undefined"]
  | .litBool b => pure [IR.IRInstr.const_ .i32 (boolAsI32 b)]
  | .litNum n => pure [IR.IRInstr.const_ .f64 (toString n)]
  | .litStr s => pure [IR.IRInstr.const_ .ptr s!"\"{s}\""]
  | .litObject addr => pure [IR.IRInstr.const_ .ptr (toString addr)]
  | .litClosure funcIdx envPtr => pure [IR.IRInstr.const_ .ptr s!"closure({funcIdx},{envPtr})"]

private def lowerTrivialM (ctx : LowerCtx) (t : ANF.Trivial) : LowerM (List IR.IRInstr) :=
  match lowerTrivial ctx t with
  | .ok code => pure code
  | .error err => throw err

private def lowerTrivialList (ctx : LowerCtx) (ts : List ANF.Trivial) : LowerM (List IR.IRInstr) := do
  let mut out := []
  for t in ts do
    out := out ++ (← lowerTrivialM ctx t)
  pure out

private partial def lowerComplex (ctx : LowerCtx) : ANF.ComplexExpr → LowerM (List IR.IRInstr)
  | .trivial t => lowerTrivialM ctx t
  | .assign name value => do
      let idx ←
        match lookupLocal ctx name with
        | .ok idx => pure idx
        | .error err => throw err
      let valueCode ← lowerTrivialM ctx value
      pure (valueCode ++ [IR.IRInstr.localSet idx, IR.IRInstr.localGet idx])
  | .call callee env args => do
      let calleeCode ← lowerTrivialM ctx callee
      let envCode ← lowerTrivialM ctx env
      let argsCode ← lowerTrivialList ctx args
      pure (calleeCode ++ envCode ++ argsCode ++ [IR.IRInstr.call RuntimeIdx.call])
  | .newObj callee env args => do
      let calleeCode ← lowerTrivialM ctx callee
      let envCode ← lowerTrivialM ctx env
      let argsCode ← lowerTrivialList ctx args
      pure (calleeCode ++ envCode ++ argsCode ++ [IR.IRInstr.call RuntimeIdx.construct])
  | .getProp obj prop => do
      let objCode ← lowerTrivialM ctx obj
      pure (objCode ++ [IR.IRInstr.const_ .ptr s!"\"{prop}\"", IR.IRInstr.call RuntimeIdx.getProp])
  | .setProp obj prop value => do
      let objCode ← lowerTrivialM ctx obj
      let valCode ← lowerTrivialM ctx value
      pure
        (objCode ++ [IR.IRInstr.const_ .ptr s!"\"{prop}\""] ++ valCode ++
          [IR.IRInstr.call RuntimeIdx.setProp])
  | .getIndex obj idx => do
      let objCode ← lowerTrivialM ctx obj
      let idxCode ← lowerTrivialM ctx idx
      pure (objCode ++ idxCode ++ [IR.IRInstr.call RuntimeIdx.getIndex])
  | .setIndex obj idx value => do
      let objCode ← lowerTrivialM ctx obj
      let idxCode ← lowerTrivialM ctx idx
      let valCode ← lowerTrivialM ctx value
      pure (objCode ++ idxCode ++ valCode ++ [IR.IRInstr.call RuntimeIdx.setIndex])
  | .deleteProp obj prop => do
      let objCode ← lowerTrivialM ctx obj
      pure (objCode ++ [IR.IRInstr.const_ .ptr s!"\"{prop}\"", IR.IRInstr.call RuntimeIdx.deleteProp])
  | .typeof arg => do
      let argCode ← lowerTrivialM ctx arg
      pure (argCode ++ [IR.IRInstr.call RuntimeIdx.typeofOp])
  | .getEnv env idx => do
      let envCode ← lowerTrivialM ctx env
      pure (envCode ++ [IR.IRInstr.const_ .i32 (toString idx), IR.IRInstr.call RuntimeIdx.getEnv])
  | .makeEnv values => do
      let valuesCode ← lowerTrivialList ctx values
      pure (valuesCode ++ [IR.IRInstr.call RuntimeIdx.makeEnv])
  | .makeClosure funcIdx env => do
      let envCode ← lowerTrivialM ctx env
      pure
        ([IR.IRInstr.const_ .i32 (toString funcIdx)] ++ envCode ++
          [IR.IRInstr.call RuntimeIdx.makeClosure])
  | .objectLit props => do
      let mut out := []
      for (prop, value) in props do
        out := out ++ [IR.IRInstr.const_ .ptr s!"\"{prop}\""] ++ (← lowerTrivialM ctx value)
      pure (out ++ [IR.IRInstr.call RuntimeIdx.objectLit])
  | .arrayLit elems => do
      let elemsCode ← lowerTrivialList ctx elems
      pure (elemsCode ++ [IR.IRInstr.call RuntimeIdx.arrayLit])
  | .unary op arg => do
      let argCode ← lowerTrivialM ctx arg
      pure (argCode ++ [IR.IRInstr.unOp .ptr (lowerUnaryOp op)])
  | .binary op lhs rhs => do
      let lhsCode ← lowerTrivialM ctx lhs
      let rhsCode ← lowerTrivialM ctx rhs
      pure (lhsCode ++ rhsCode ++ [IR.IRInstr.binOp .ptr (lowerBinOp op)])

private partial def lowerExpr (ctx : LowerCtx) : ANF.Expr → LowerM (List IR.IRInstr)
  | .trivial t => lowerTrivialM ctx t
  | .«let» name rhs body => do
      let rhsCode ← lowerComplex ctx rhs
      let (idx, ctx') ← allocLocal name ctx
      let bodyCode ← lowerExpr ctx' body
      pure (rhsCode ++ [IR.IRInstr.localSet idx] ++ bodyCode)
  | .seq a b => do
      let aCode ← lowerExpr ctx a
      let bCode ← lowerExpr ctx b
      pure (aCode ++ [IR.IRInstr.drop] ++ bCode)
  | .«if» cond then_ else_ => do
      let condCode ← lowerTrivialM ctx cond
      let thenCode ← lowerExpr ctx then_
      let elseCode ← lowerExpr ctx else_
      pure (condCode ++ [IR.IRInstr.if_ thenCode elseCode])
  | .while_ cond body => do
      let condCode ← lowerExpr ctx cond
      let bodyCode ← lowerExpr ctx body
      pure
        [IR.IRInstr.block "while_exit"
          [IR.IRInstr.loop "while_loop"
            (condCode ++
              [IR.IRInstr.unOp .i32 "eqz", IR.IRInstr.brIf "while_exit"] ++
              bodyCode ++
              [IR.IRInstr.drop, IR.IRInstr.br "while_loop"])]]
  | .throw arg => do
      let argCode ← lowerTrivialM ctx arg
      pure (argCode ++ [IR.IRInstr.call RuntimeIdx.throwOp, IR.IRInstr.return_])
  | .tryCatch body _ catchBody finally_ => do
      let bodyCode ← lowerExpr ctx body
      let catchCode ← lowerExpr ctx catchBody
      let finallyCode ←
        match finally_ with
        | some f => lowerExpr ctx f
        | none => pure []
      pure
        [IR.IRInstr.block "try"
          (bodyCode ++ [IR.IRInstr.br "try_end"] ++ catchCode ++ finallyCode ++
            [IR.IRInstr.block "try_end" []])]
  | .«return» arg =>
      match arg with
      | some v => do
          let code ← lowerTrivialM ctx v
          pure (code ++ [IR.IRInstr.return_])
      | none => pure [IR.IRInstr.return_]
  | .yield arg delegate => do
      let argCode ←
        match arg with
        | some v => lowerTrivialM ctx v
        | none => pure [IR.IRInstr.const_ .ptr "undefined"]
      pure
        (argCode ++
          [IR.IRInstr.const_ .i32 (boolAsI32 delegate), IR.IRInstr.call RuntimeIdx.yieldOp])
  | .await arg => do
      let argCode ← lowerTrivialM ctx arg
      pure (argCode ++ [IR.IRInstr.call RuntimeIdx.awaitOp])
  | .labeled label body => do
      let bodyCode ← lowerExpr ctx body
      pure [IR.IRInstr.block label bodyCode]
  | .«break» label =>
      pure [IR.IRInstr.br (label.getD "break")]
  | .«continue» label =>
      pure [IR.IRInstr.br (label.getD "continue")]

private def mkInitialCtx (params : List ANF.VarName) (envParam : ANF.VarName) : LowerCtx :=
  let rec go (ps : List ANF.VarName) (idx : Nat) (acc : List (ANF.VarName × Nat)) :
      List (ANF.VarName × Nat) :=
    match ps with
    | [] => acc
    | p :: rest => go rest (idx + 1) ((p, idx) :: acc)
  let envIdx := params.length
  { locals := (envParam, envIdx) :: go params 0 [] }

private def lowerFunction (f : ANF.FuncDef) : Except String IR.IRFunc := do
  let paramTypes := List.replicate (f.params.length + 1) IR.IRType.ptr
  let initState : LowerState := { nextLocal := paramTypes.length, locals := #[] }
  let ctx := mkInitialCtx f.params f.envParam
  let (body, st) ← (lowerExpr ctx f.body).run initState
  pure
    { name := f.name
      params := paramTypes
      results := [IR.IRType.ptr]
      locals := st.locals.toList
      body := body }

/-- Lower an ANF program to Wasm IR. ECMA-262 runtime behavior is preserved structurally via ANF sequencing (§13). -/
def lower (prog : ANF.Program) : Except String IR.IRModule := do
  let loweredFns ← prog.functions.toList.mapM lowerFunction
  let mainFn : ANF.FuncDef :=
    { name := "__verifiedjs_main"
      params := []
      envParam := "__env"
      body := prog.main }
  let loweredMain ← lowerFunction mainFn
  let functions := (loweredFns ++ [loweredMain]).toArray
  let mainIdx := loweredFns.length
  pure
    { functions := functions
      memories := #[{ lim := { min := 1, max := none } }]
      globals := #[]
      exports := #[("main", mainIdx)]
      dataSegments := #[]
      startFunc := some mainIdx }

end VerifiedJS.Wasm
