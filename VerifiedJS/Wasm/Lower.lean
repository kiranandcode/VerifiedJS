/-
  VerifiedJS — Lowering: JS.ANF → Wasm.IR
-/

import VerifiedJS.ANF.Syntax
import VerifiedJS.Runtime.Values
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
def toNumber : RuntimeFuncIdx := 16
def encodeNumber : RuntimeFuncIdx := 17
def truthy : RuntimeFuncIdx := 18
def encodeBool : RuntimeFuncIdx := 19
def unaryNeg : RuntimeFuncIdx := 20
def unaryPos : RuntimeFuncIdx := 21
def unaryLogNot : RuntimeFuncIdx := 22
def binaryAdd : RuntimeFuncIdx := 23
def binarySub : RuntimeFuncIdx := 24
def binaryMul : RuntimeFuncIdx := 25
def binaryDiv : RuntimeFuncIdx := 26
def binaryMod : RuntimeFuncIdx := 27
def binaryLt : RuntimeFuncIdx := 28
def binaryGt : RuntimeFuncIdx := 29
def binaryLe : RuntimeFuncIdx := 30
def binaryGe : RuntimeFuncIdx := 31
def binaryEq : RuntimeFuncIdx := 32
def binaryNeq : RuntimeFuncIdx := 33

end RuntimeIdx

structure LowerCtx where
  locals : List (ANF.VarName × Nat)
  deriving Inhabited

structure LowerState where
  nextLocal : Nat
  locals : Array IR.IRType
  nextStringId : Nat
  strings : List (String × Nat)
  deriving Inhabited

abbrev LowerM := StateT LowerState (Except String)

private def lookupLocal (ctx : LowerCtx) (name : ANF.VarName) : Except String Nat :=
  match ctx.locals.find? (fun pair => pair.fst = name) with
  | some (_, idx) => .ok idx
  | none => .error s!"lower: unbound variable '{name}'"

private def allocLocal (name : ANF.VarName) (ctx : LowerCtx) : LowerM (Nat × LowerCtx) := do
  let st ← get
  let idx := st.nextLocal
  set { st with nextLocal := idx + 1, locals := st.locals.push .f64 }
  pure (idx, { ctx with locals := (name, idx) :: ctx.locals })

private def mkF64BitsConst (bits : UInt64) : IR.IRInstr :=
  IR.IRInstr.const_ .f64 s!"bits:{bits.toNat}"

private def mkBoxedConst (v : Runtime.NanBoxed) : IR.IRInstr :=
  mkF64BitsConst v.bits

private def encodeNatAsInt32 (n : Nat) : Runtime.NanBoxed :=
  Runtime.NanBoxed.encodeInt32 (Int32.ofInt (Int.ofNat n))

private def encodeBoolBox (b : Bool) : Runtime.NanBoxed :=
  Runtime.NanBoxed.encodeBool b

private def encodeUndefinedBox : Runtime.NanBoxed :=
  Runtime.NanBoxed.encodeUndefined

private def encodeNullBox : Runtime.NanBoxed :=
  Runtime.NanBoxed.encodeNull

private def internString (s : String) : LowerM Nat := do
  let st ← get
  match st.strings.find? (fun (name, _) => name = s) with
  | some (_, idx) => pure idx
  | none =>
      let idx := st.nextStringId
      set { st with nextStringId := idx + 1, strings := (s, idx) :: st.strings }
      pure idx

private def mkStringRefConstM (s : String) : LowerM IR.IRInstr := do
  let sid ← internString s
  pure <| mkBoxedConst (Runtime.NanBoxed.encodeStringRef sid)

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

private def lowerUnaryRuntime? : Core.UnaryOp → Option RuntimeFuncIdx
  | .neg => some RuntimeIdx.unaryNeg
  | .pos => some RuntimeIdx.unaryPos
  | .logNot => some RuntimeIdx.unaryLogNot
  | _ => none

private def lowerBinaryRuntime? : Core.BinOp → Option RuntimeFuncIdx
  | .add => some RuntimeIdx.binaryAdd
  | .sub => some RuntimeIdx.binarySub
  | .mul => some RuntimeIdx.binaryMul
  | .div => some RuntimeIdx.binaryDiv
  | .mod => some RuntimeIdx.binaryMod
  | .lt => some RuntimeIdx.binaryLt
  | .gt => some RuntimeIdx.binaryGt
  | .le => some RuntimeIdx.binaryLe
  | .ge => some RuntimeIdx.binaryGe
  | .eq | .strictEq => some RuntimeIdx.binaryEq
  | .neq | .strictNeq => some RuntimeIdx.binaryNeq
  | _ => none

private def drops (n : Nat) : List IR.IRInstr :=
  List.replicate n IR.IRInstr.drop

private def lowerTrivial (ctx : LowerCtx) : ANF.Trivial → LowerM (List IR.IRInstr)
  | .var name =>
      match lookupLocal ctx name with
      | .ok idx => pure [IR.IRInstr.localGet idx]
      | .error err => throw err
  -- JS values are carried as NaN-boxed bit patterns reinterpreted as f64.
  | .litNull => pure [mkBoxedConst encodeNullBox]
  | .litUndefined => pure [mkBoxedConst encodeUndefinedBox]
  | .litBool b => pure [mkBoxedConst (encodeBoolBox b)]
  | .litNum n => pure [mkBoxedConst (Runtime.NanBoxed.encodeNumber n)]
  | .litStr s => do
      let sid ← internString s
      pure [mkBoxedConst (Runtime.NanBoxed.encodeStringRef sid)]
  | .litObject addr => pure [mkBoxedConst (Runtime.NanBoxed.encodeObjectRef addr)]
  | .litClosure funcIdx envPtr =>
      pure [mkBoxedConst (Runtime.NanBoxed.encodeObjectRef (funcIdx * 65536 + envPtr))]

private def lowerTrivialM (ctx : LowerCtx) (t : ANF.Trivial) : LowerM (List IR.IRInstr) :=
  lowerTrivial ctx t

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
      pure
        (calleeCode ++ envCode ++ argsCode ++ drops args.length ++
          [IR.IRInstr.call RuntimeIdx.call])
  | .newObj callee env args => do
      let calleeCode ← lowerTrivialM ctx callee
      let envCode ← lowerTrivialM ctx env
      let argsCode ← lowerTrivialList ctx args
      pure
        (calleeCode ++ envCode ++ argsCode ++ drops args.length ++
          [IR.IRInstr.call RuntimeIdx.construct])
  | .getProp obj prop => do
      let objCode ← lowerTrivialM ctx obj
      let propCode ← mkStringRefConstM prop
      pure (objCode ++ [propCode, IR.IRInstr.call RuntimeIdx.getProp])
  | .setProp obj prop value => do
      let objCode ← lowerTrivialM ctx obj
      let valCode ← lowerTrivialM ctx value
      let propCode ← mkStringRefConstM prop
      pure
        (objCode ++ [propCode] ++ valCode ++
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
      let propCode ← mkStringRefConstM prop
      pure (objCode ++ [propCode, IR.IRInstr.call RuntimeIdx.deleteProp])
  | .typeof arg => do
      let argCode ← lowerTrivialM ctx arg
      pure (argCode ++ [IR.IRInstr.call RuntimeIdx.typeofOp])
  | .getEnv env idx => do
      let envCode ← lowerTrivialM ctx env
      pure (envCode ++ [mkBoxedConst (encodeNatAsInt32 idx), IR.IRInstr.call RuntimeIdx.getEnv])
  | .makeEnv values => do
      let valuesCode ← lowerTrivialList ctx values
      pure (valuesCode ++ drops values.length ++ [IR.IRInstr.call RuntimeIdx.makeEnv])
  | .makeClosure funcIdx env => do
      let envCode ← lowerTrivialM ctx env
      pure
        ([mkBoxedConst (encodeNatAsInt32 funcIdx)] ++ envCode ++
          [IR.IRInstr.call RuntimeIdx.makeClosure])
  | .objectLit props => do
      let mut out := []
      for (prop, value) in props do
        let propCode ← mkStringRefConstM prop
        out := out ++ [propCode] ++ (← lowerTrivialM ctx value)
      pure (out ++ drops (2 * props.length) ++ [IR.IRInstr.call RuntimeIdx.objectLit])
  | .arrayLit elems => do
      let elemsCode ← lowerTrivialList ctx elems
      pure (elemsCode ++ drops elems.length ++ [IR.IRInstr.call RuntimeIdx.arrayLit])
  | .unary op arg => do
      let argCode ← lowerTrivialM ctx arg
      match lowerUnaryRuntime? op with
      | some fn => pure (argCode ++ [IR.IRInstr.call fn])
      | none => pure (argCode ++ [IR.IRInstr.unOp .f64 (lowerUnaryOp op)])
  | .binary op lhs rhs => do
      let lhsCode ← lowerTrivialM ctx lhs
      let rhsCode ← lowerTrivialM ctx rhs
      match lowerBinaryRuntime? op with
      | some fn => pure (lhsCode ++ rhsCode ++ [IR.IRInstr.call fn])
      | none => pure (lhsCode ++ rhsCode ++ [IR.IRInstr.binOp .f64 (lowerBinOp op)])

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
      pure (condCode ++ [IR.IRInstr.call RuntimeIdx.truthy, IR.IRInstr.if_ thenCode elseCode])
  | .while_ cond body => do
      let condCode ← lowerExpr ctx cond
      let bodyCode ← lowerExpr ctx body
      pure
        [IR.IRInstr.block "while_exit"
          [IR.IRInstr.loop "while_loop"
            (condCode ++
              [IR.IRInstr.call RuntimeIdx.truthy, IR.IRInstr.unOp .i32 "eqz",
                IR.IRInstr.brIf "while_exit"] ++
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
        | none => pure [mkBoxedConst encodeUndefinedBox]
      pure
        (argCode ++
          [mkBoxedConst (encodeBoolBox delegate), IR.IRInstr.call RuntimeIdx.yieldOp])
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
  let paramTypes := List.replicate (f.params.length + 1) IR.IRType.f64
  let initState : LowerState :=
    { nextLocal := paramTypes.length, locals := #[], nextStringId := 0, strings := [] }
  let ctx := mkInitialCtx f.params f.envParam
  let (body, st) ← (lowerExpr ctx f.body).run initState
  pure
    { name := f.name
      params := paramTypes
      results := [IR.IRType.f64]
      locals := st.locals.toList
      body := body }

/-- Build a preamble that binds each top-level function name to its closure value. -/
private def buildFuncBindings (funcs : Array ANF.FuncDef) (mainBody : ANF.Expr) (baseIdx : Nat) :
    ANF.Expr :=
  let rec go (i : Nat) (fns : List ANF.FuncDef) (body : ANF.Expr) : ANF.Expr :=
    match fns with
    | [] => body
    | f :: rest =>
      -- Bind function name to a makeClosure(funcIdx, null_env)
      .«let» f.name (.makeClosure (baseIdx + i) (.litNull)) (go (i + 1) rest body)
  go 0 funcs.toList mainBody

private def runtimeHelpers : Array IR.IRFunc :=
  #[
    { name := "__rt_call", params := [.f64, .f64], results := [.f64], locals := []
      body := [mkBoxedConst encodeUndefinedBox, IR.IRInstr.return_] },
    { name := "__rt_construct", params := [.f64, .f64], results := [.f64], locals := []
      body := [mkBoxedConst (Runtime.NanBoxed.encodeObjectRef 0), IR.IRInstr.return_] },
    { name := "__rt_getProp", params := [.f64, .f64], results := [.f64], locals := []
      body := [mkBoxedConst encodeUndefinedBox, IR.IRInstr.return_] },
    { name := "__rt_setProp", params := [.f64, .f64, .f64], results := [.f64], locals := []
      body := [mkBoxedConst encodeUndefinedBox, IR.IRInstr.return_] },
    { name := "__rt_getIndex", params := [.f64, .f64], results := [.f64], locals := []
      body := [mkBoxedConst encodeUndefinedBox, IR.IRInstr.return_] },
    { name := "__rt_setIndex", params := [.f64, .f64, .f64], results := [.f64], locals := []
      body := [mkBoxedConst encodeUndefinedBox, IR.IRInstr.return_] },
    { name := "__rt_deleteProp", params := [.f64, .f64], results := [.f64], locals := []
      body := [mkBoxedConst (encodeBoolBox true), IR.IRInstr.return_] },
    { name := "__rt_typeof", params := [.f64], results := [.f64], locals := []
      body := [mkBoxedConst (Runtime.NanBoxed.encodeStringRef 0), IR.IRInstr.return_] },
    { name := "__rt_getEnv", params := [.f64, .f64], results := [.f64], locals := []
      body := [mkBoxedConst encodeUndefinedBox, IR.IRInstr.return_] },
    { name := "__rt_makeEnv", params := [], results := [.f64], locals := []
      body := [mkBoxedConst (Runtime.NanBoxed.encodeObjectRef 1), IR.IRInstr.return_] },
    { name := "__rt_makeClosure", params := [.f64, .f64], results := [.f64], locals := []
      body := [mkBoxedConst (Runtime.NanBoxed.encodeObjectRef 2), IR.IRInstr.return_] },
    { name := "__rt_objectLit", params := [], results := [.f64], locals := []
      body := [mkBoxedConst (Runtime.NanBoxed.encodeObjectRef 3), IR.IRInstr.return_] },
    { name := "__rt_arrayLit", params := [], results := [.f64], locals := []
      body := [mkBoxedConst (Runtime.NanBoxed.encodeObjectRef 4), IR.IRInstr.return_] },
    { name := "__rt_throw", params := [.f64], results := [.f64], locals := []
      body := [mkBoxedConst encodeUndefinedBox, IR.IRInstr.return_] },
    { name := "__rt_yield", params := [.f64, .f64], results := [.f64], locals := []
      body := [mkBoxedConst encodeUndefinedBox, IR.IRInstr.return_] },
    { name := "__rt_await", params := [.f64], results := [.f64], locals := []
      body := [mkBoxedConst encodeUndefinedBox, IR.IRInstr.return_] }
    ,
    { name := "__rt_toNumber", params := [.f64], results := [.f64], locals := [.i64, .i64]
      body :=
        [ IR.IRInstr.localGet 0
        , IR.IRInstr.unOp .i64 "reinterpret_f64"
        , IR.IRInstr.localSet 1
        , IR.IRInstr.localGet 1
        , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.nanMask.toNat}"
        , IR.IRInstr.binOp .i64 "and"
        , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.nanMask.toNat}"
        , IR.IRInstr.binOp .i64 "eq"
        , IR.IRInstr.if_
            [ IR.IRInstr.localGet 1
            , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.tagMask.toNat}"
            , IR.IRInstr.binOp .i64 "and"
            , IR.IRInstr.localSet 2
            , IR.IRInstr.localGet 2
            , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.tagNull.toNat}"
            , IR.IRInstr.binOp .i64 "eq"
            , IR.IRInstr.if_
                [IR.IRInstr.const_ .f64 "0.0"]
                [ IR.IRInstr.localGet 2
                , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.tagUndefined.toNat}"
                , IR.IRInstr.binOp .i64 "eq"
                , IR.IRInstr.if_
                    [mkBoxedConst (Runtime.NanBoxed.encodeNumber (0.0 / 0.0))]
                    [ IR.IRInstr.localGet 2
                    , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.tagBool.toNat}"
                    , IR.IRInstr.binOp .i64 "eq"
                    , IR.IRInstr.if_
                        [ IR.IRInstr.localGet 1
                        , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.payloadMask.toNat}"
                        , IR.IRInstr.binOp .i64 "and"
                        , IR.IRInstr.unOp .i64 "eqz"
                        , IR.IRInstr.unOp .i32 "eqz"
                        , IR.IRInstr.if_ [IR.IRInstr.const_ .f64 "1.0"] [IR.IRInstr.const_ .f64 "0.0"] ]
                        [ IR.IRInstr.localGet 2
                        , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.tagInt32.toNat}"
                        , IR.IRInstr.binOp .i64 "eq"
                        , IR.IRInstr.if_
                            [ IR.IRInstr.localGet 1
                            , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.payloadMask.toNat}"
                            , IR.IRInstr.binOp .i64 "and"
                            , IR.IRInstr.unOp .i32 "wrap_i64"
                            , IR.IRInstr.unOp .f64 "convert_i32_s" ]
                            [mkBoxedConst (Runtime.NanBoxed.encodeNumber (0.0 / 0.0))] ] ] ] ]
            [IR.IRInstr.localGet 0]
        , IR.IRInstr.return_ ] }
    ,
    { name := "__rt_encodeNumber", params := [.f64], results := [.f64], locals := []
      body :=
        [ IR.IRInstr.localGet 0
        , IR.IRInstr.localGet 0
        , IR.IRInstr.binOp .f64 "raw_eq"
        , IR.IRInstr.if_
            [IR.IRInstr.localGet 0]
            [mkBoxedConst (Runtime.NanBoxed.encodeNumber (0.0 / 0.0))]
        , IR.IRInstr.return_ ] }
    ,
    { name := "__rt_truthy", params := [.f64], results := [.i32], locals := [.i64, .i64]
      body :=
        [ IR.IRInstr.localGet 0
        , IR.IRInstr.unOp .i64 "reinterpret_f64"
        , IR.IRInstr.localSet 1
        , IR.IRInstr.localGet 1
        , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.nanMask.toNat}"
        , IR.IRInstr.binOp .i64 "and"
        , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.nanMask.toNat}"
        , IR.IRInstr.binOp .i64 "eq"
        , IR.IRInstr.if_
            [ IR.IRInstr.localGet 1
            , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.tagMask.toNat}"
            , IR.IRInstr.binOp .i64 "and"
            , IR.IRInstr.localSet 2
            , IR.IRInstr.localGet 2
            , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.tagNull.toNat}"
            , IR.IRInstr.binOp .i64 "eq"
            , IR.IRInstr.if_
                [IR.IRInstr.const_ .i32 "0"]
                [ IR.IRInstr.localGet 2
                , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.tagUndefined.toNat}"
                , IR.IRInstr.binOp .i64 "eq"
                , IR.IRInstr.if_
                    [IR.IRInstr.const_ .i32 "0"]
                    [ IR.IRInstr.localGet 2
                    , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.tagBool.toNat}"
                    , IR.IRInstr.binOp .i64 "eq"
                    , IR.IRInstr.if_
                        [ IR.IRInstr.localGet 1
                        , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.payloadMask.toNat}"
                        , IR.IRInstr.binOp .i64 "and"
                        , IR.IRInstr.unOp .i64 "eqz"
                        , IR.IRInstr.unOp .i32 "eqz" ]
                        [ IR.IRInstr.localGet 2
                        , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.tagInt32.toNat}"
                        , IR.IRInstr.binOp .i64 "eq"
                        , IR.IRInstr.if_
                            [ IR.IRInstr.localGet 1
                            , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.payloadMask.toNat}"
                            , IR.IRInstr.binOp .i64 "and"
                            , IR.IRInstr.unOp .i64 "eqz"
                            , IR.IRInstr.unOp .i32 "eqz" ]
                            [IR.IRInstr.const_ .i32 "1"] ] ] ] ]
            [ IR.IRInstr.localGet 0
            , IR.IRInstr.localGet 0
            , IR.IRInstr.binOp .f64 "raw_eq"
            , IR.IRInstr.localGet 0
            , IR.IRInstr.const_ .f64 "0.0"
            , IR.IRInstr.binOp .f64 "raw_ne"
            , IR.IRInstr.binOp .i32 "and" ]
        , IR.IRInstr.return_ ] }
    ,
    { name := "__rt_encodeBool", params := [.i32], results := [.f64], locals := []
      body :=
        [ IR.IRInstr.localGet 0
        , IR.IRInstr.if_
            [mkBoxedConst (encodeBoolBox true)]
            [mkBoxedConst (encodeBoolBox false)]
        , IR.IRInstr.return_ ] }
    ,
    { name := "__rt_unaryNeg", params := [.f64], results := [.f64], locals := []
      body :=
        [ IR.IRInstr.localGet 0
        , IR.IRInstr.call RuntimeIdx.toNumber
        , IR.IRInstr.unOp .f64 "neg_raw"
        , IR.IRInstr.call RuntimeIdx.encodeNumber
        , IR.IRInstr.return_ ] }
    ,
    { name := "__rt_unaryPos", params := [.f64], results := [.f64], locals := []
      body :=
        [ IR.IRInstr.localGet 0
        , IR.IRInstr.call RuntimeIdx.toNumber
        , IR.IRInstr.call RuntimeIdx.encodeNumber
        , IR.IRInstr.return_ ] }
    ,
    { name := "__rt_unaryLogNot", params := [.f64], results := [.f64], locals := []
      body :=
        [ IR.IRInstr.localGet 0
        , IR.IRInstr.call RuntimeIdx.truthy
        , IR.IRInstr.unOp .i32 "eqz"
        , IR.IRInstr.call RuntimeIdx.encodeBool
        , IR.IRInstr.return_ ] }
    ,
    { name := "__rt_binaryAdd", params := [.f64, .f64], results := [.f64], locals := []
      body := [IR.IRInstr.localGet 0, IR.IRInstr.call RuntimeIdx.toNumber, IR.IRInstr.localGet 1,
        IR.IRInstr.call RuntimeIdx.toNumber, IR.IRInstr.binOp .f64 "add_raw",
        IR.IRInstr.call RuntimeIdx.encodeNumber, IR.IRInstr.return_] }
    ,
    { name := "__rt_binarySub", params := [.f64, .f64], results := [.f64], locals := []
      body := [IR.IRInstr.localGet 0, IR.IRInstr.call RuntimeIdx.toNumber, IR.IRInstr.localGet 1,
        IR.IRInstr.call RuntimeIdx.toNumber, IR.IRInstr.binOp .f64 "sub_raw",
        IR.IRInstr.call RuntimeIdx.encodeNumber, IR.IRInstr.return_] }
    ,
    { name := "__rt_binaryMul", params := [.f64, .f64], results := [.f64], locals := []
      body := [IR.IRInstr.localGet 0, IR.IRInstr.call RuntimeIdx.toNumber, IR.IRInstr.localGet 1,
        IR.IRInstr.call RuntimeIdx.toNumber, IR.IRInstr.binOp .f64 "mul_raw",
        IR.IRInstr.call RuntimeIdx.encodeNumber, IR.IRInstr.return_] }
    ,
    { name := "__rt_binaryDiv", params := [.f64, .f64], results := [.f64], locals := []
      body := [IR.IRInstr.localGet 0, IR.IRInstr.call RuntimeIdx.toNumber, IR.IRInstr.localGet 1,
        IR.IRInstr.call RuntimeIdx.toNumber, IR.IRInstr.binOp .f64 "div_raw",
        IR.IRInstr.call RuntimeIdx.encodeNumber, IR.IRInstr.return_] }
    ,
    { name := "__rt_binaryMod", params := [.f64, .f64], results := [.f64], locals := []
      body := [IR.IRInstr.localGet 0, IR.IRInstr.call RuntimeIdx.toNumber, IR.IRInstr.localGet 1,
        IR.IRInstr.call RuntimeIdx.toNumber, IR.IRInstr.binOp .f64 "mod_raw",
        IR.IRInstr.call RuntimeIdx.encodeNumber, IR.IRInstr.return_] }
    ,
    { name := "__rt_binaryLt", params := [.f64, .f64], results := [.f64], locals := []
      body := [IR.IRInstr.localGet 0, IR.IRInstr.call RuntimeIdx.toNumber, IR.IRInstr.localGet 1,
        IR.IRInstr.call RuntimeIdx.toNumber, IR.IRInstr.binOp .f64 "raw_lt",
        IR.IRInstr.call RuntimeIdx.encodeBool, IR.IRInstr.return_] }
    ,
    { name := "__rt_binaryGt", params := [.f64, .f64], results := [.f64], locals := []
      body := [IR.IRInstr.localGet 0, IR.IRInstr.call RuntimeIdx.toNumber, IR.IRInstr.localGet 1,
        IR.IRInstr.call RuntimeIdx.toNumber, IR.IRInstr.binOp .f64 "raw_gt",
        IR.IRInstr.call RuntimeIdx.encodeBool, IR.IRInstr.return_] }
    ,
    { name := "__rt_binaryLe", params := [.f64, .f64], results := [.f64], locals := []
      body := [IR.IRInstr.localGet 0, IR.IRInstr.call RuntimeIdx.toNumber, IR.IRInstr.localGet 1,
        IR.IRInstr.call RuntimeIdx.toNumber, IR.IRInstr.binOp .f64 "raw_le",
        IR.IRInstr.call RuntimeIdx.encodeBool, IR.IRInstr.return_] }
    ,
    { name := "__rt_binaryGe", params := [.f64, .f64], results := [.f64], locals := []
      body := [IR.IRInstr.localGet 0, IR.IRInstr.call RuntimeIdx.toNumber, IR.IRInstr.localGet 1,
        IR.IRInstr.call RuntimeIdx.toNumber, IR.IRInstr.binOp .f64 "raw_ge",
        IR.IRInstr.call RuntimeIdx.encodeBool, IR.IRInstr.return_] }
    ,
    { name := "__rt_binaryEq", params := [.f64, .f64], results := [.f64], locals := []
      body := [IR.IRInstr.localGet 0, IR.IRInstr.call RuntimeIdx.toNumber, IR.IRInstr.localGet 1,
        IR.IRInstr.call RuntimeIdx.toNumber, IR.IRInstr.binOp .f64 "raw_eq",
        IR.IRInstr.call RuntimeIdx.encodeBool, IR.IRInstr.return_] }
    ,
    { name := "__rt_binaryNeq", params := [.f64, .f64], results := [.f64], locals := []
      body := [IR.IRInstr.localGet 0, IR.IRInstr.call RuntimeIdx.toNumber, IR.IRInstr.localGet 1,
        IR.IRInstr.call RuntimeIdx.toNumber, IR.IRInstr.binOp .f64 "raw_ne",
        IR.IRInstr.call RuntimeIdx.encodeBool, IR.IRInstr.return_] }
  ]

/-- Lower an ANF program to Wasm IR. ECMA-262 runtime behavior is preserved structurally via ANF sequencing (§13). -/
def lower (prog : ANF.Program) : Except String IR.IRModule := do
  let runtimeCount := runtimeHelpers.size
  let loweredFns ← prog.functions.toList.mapM lowerFunction
  -- Wrap main body with top-level function bindings
  let wrappedMain := buildFuncBindings prog.functions prog.main runtimeCount
  let mainFn : ANF.FuncDef :=
    { name := "__verifiedjs_main"
      params := []
      envParam := "__env"
      body := wrappedMain }
  let loweredMain ← lowerFunction mainFn
  let mainIdx := runtimeCount + loweredFns.length
  -- Create a _start wrapper with zero params/results (Wasm spec requires this for start func)
  let startWrapper : IR.IRFunc :=
    { name := "_start"
      params := []
      results := []
      locals := []
      body := [mkBoxedConst encodeUndefinedBox, IR.IRInstr.call mainIdx, IR.IRInstr.drop] }
  let startIdx := mainIdx + 1
  let functions := runtimeHelpers ++ loweredFns.toArray ++ #[loweredMain, startWrapper]
  pure
    { functions := functions
      memories := #[{ lim := { min := 1, max := none } }]
      globals := #[]
      exports := #[("main", mainIdx), ("_start", startIdx)]
      dataSegments := #[]
      startFunc := some startIdx }

end VerifiedJS.Wasm
