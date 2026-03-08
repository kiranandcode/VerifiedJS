/-
  VerifiedJS — Closure Conversion: JS.Core → JS.Flat
  Converts closures to (function_index, environment_pointer) pairs.
-/

import VerifiedJS.Core.Syntax
import VerifiedJS.Flat.Syntax

namespace VerifiedJS.Flat

/-- Captured-variable context for the current function body. -/
abbrev CaptureCtx := List Core.VarName

/-- Internal closure-conversion state (accumulated Flat function table). -/
structure CCState where
  funcs : Array FuncDef

abbrev CCM := StateM CCState

/-- Environment parameter name used in all closure-converted function bodies. -/
def envParamName : Core.VarName := "__env"

/-- Default expression for partial conversion recursion fallback. -/
instance : Inhabited Expr where
  default := .lit .undefined

/-- Placeholder while reserving top-level function slots. -/
def placeholderFunc : FuncDef :=
  { name := "__placeholder"
    params := []
    envParam := envParamName
    body := .lit .undefined }

/-- Convert Core values to Flat values (ECMA-262 §6.1 value domain embedding). -/
def valueToFlat : Core.Value → Value
  | .null => .null
  | .undefined => .undefined
  | .bool b => .bool b
  | .number n => .number n
  | .string s => .string s
  | .object addr => .object addr
  | .function idx => .closure idx 0

def captureIndexAux (captures : CaptureCtx) (name : Core.VarName) (i : Nat) : Option Nat :=
  match captures with
  | [] => none
  | c :: rest =>
      if c == name then
        some i
      else
        captureIndexAux rest name (i + 1)

/-- Find the capture index for a variable name in the current closure context. -/
def captureIndex? (captures : CaptureCtx) (name : Core.VarName) : Option Nat :=
  captureIndexAux captures name 0

/-- Convert variable references; captured vars are read from environment tuples. -/
def convertVarRef (captures : CaptureCtx) (name : Core.VarName) : Expr :=
  match captureIndex? captures name with
  | some idx => .getEnv (.var envParamName) idx
  | none => .var name

def insertUnique (xs : List Core.VarName) (x : Core.VarName) : List Core.VarName :=
  if xs.contains x then xs else x :: xs

def unionUnique (xs ys : List Core.VarName) : List Core.VarName :=
  ys.foldl insertUnique xs

def eraseAll (xs names : List Core.VarName) : List Core.VarName :=
  names.foldl List.erase xs

/-- Free variable approximation used for closure capture lists. -/
partial def freeVars : Core.Expr → List Core.VarName
  | .lit _ => []
  | .var name => [name]
  | .let name init body => eraseAll (unionUnique (freeVars init) (freeVars body)) [name]
  | .assign name value => insertUnique (freeVars value) name
  | .if cond then_ else_ => unionUnique (freeVars cond) (unionUnique (freeVars then_) (freeVars else_))
  | .seq a b => unionUnique (freeVars a) (freeVars b)
  | .call callee args => args.foldl (fun acc arg => unionUnique acc (freeVars arg)) (freeVars callee)
  | .newObj callee args => args.foldl (fun acc arg => unionUnique acc (freeVars arg)) (freeVars callee)
  | .getProp obj _ => freeVars obj
  | .setProp obj _ value => unionUnique (freeVars obj) (freeVars value)
  | .getIndex obj idx => unionUnique (freeVars obj) (freeVars idx)
  | .setIndex obj idx value => unionUnique (unionUnique (freeVars obj) (freeVars idx)) (freeVars value)
  | .deleteProp obj _ => freeVars obj
  | .typeof arg => freeVars arg
  | .unary _ arg => freeVars arg
  | .binary _ lhs rhs => unionUnique (freeVars lhs) (freeVars rhs)
  | .objectLit props => props.foldl (fun acc p => unionUnique acc (freeVars p.snd)) []
  | .arrayLit elems => elems.foldl (fun acc e => unionUnique acc (freeVars e)) []
  | .functionDef name params body _ _ =>
      let bound := match name with
        | some n => n :: params
        | none => params
      eraseAll (freeVars body) bound
  | .throw arg => freeVars arg
  | .tryCatch body catchParam catchBody finally_ =>
      let withCatch := unionUnique (freeVars body) (eraseAll (freeVars catchBody) [catchParam])
      match finally_ with
      | some f => unionUnique withCatch (freeVars f)
      | none => withCatch
  | .while_ cond body => unionUnique (freeVars cond) (freeVars body)
  | .break _ => []
  | .continue _ => []
  | .return arg =>
      match arg with
      | some e => freeVars e
      | none => []
  | .labeled _ body => freeVars body
  | .yield arg _ =>
      match arg with
      | some e => freeVars e
      | none => []
  | .await arg => freeVars arg
  | .this => []

def appendFunc (f : FuncDef) : CCM FuncIdx := do
  let st ← get
  let idx := st.funcs.size
  set { st with funcs := st.funcs.push f }
  pure idx

def setReservedFunc (idx : Nat) (f : FuncDef) : CCM Unit := do
  modify fun st => { st with funcs := st.funcs.set! idx f }

/-- ECMA-262 §10.2 closure conversion from Core expressions into first-order Flat form. -/
partial def convertExpr (captures : CaptureCtx) : Core.Expr → CCM Expr
  | .lit v => pure (.lit (valueToFlat v))
  | .var name => pure (convertVarRef captures name)
  | .let name init body => do
      let init' ← convertExpr captures init
      let body' ← convertExpr captures body
      pure (.let name init' body')
  | .assign name value => do
      let value' ← convertExpr captures value
      pure (.assign name value')
  | .if cond then_ else_ => do
      let cond' ← convertExpr captures cond
      let then' ← convertExpr captures then_
      let else' ← convertExpr captures else_
      pure (.if cond' then' else')
  | .seq a b => do
      let a' ← convertExpr captures a
      let b' ← convertExpr captures b
      pure (.seq a' b')
  | .call callee args => do
      let callee' ← convertExpr captures callee
      let args' ← args.mapM (convertExpr captures)
      pure (.call callee' (.lit (.number 0)) args')
  | .newObj callee args => do
      let callee' ← convertExpr captures callee
      let args' ← args.mapM (convertExpr captures)
      pure (.newObj callee' (.lit (.number 0)) args')
  | .getProp obj prop => do
      let obj' ← convertExpr captures obj
      pure (.getProp obj' prop)
  | .setProp obj prop value => do
      let obj' ← convertExpr captures obj
      let value' ← convertExpr captures value
      pure (.setProp obj' prop value')
  | .getIndex obj idx => do
      let obj' ← convertExpr captures obj
      let idx' ← convertExpr captures idx
      pure (.getIndex obj' idx')
  | .setIndex obj idx value => do
      let obj' ← convertExpr captures obj
      let idx' ← convertExpr captures idx
      let value' ← convertExpr captures value
      pure (.setIndex obj' idx' value')
  | .deleteProp obj prop => do
      let obj' ← convertExpr captures obj
      pure (.deleteProp obj' prop)
  | .typeof arg => do
      let arg' ← convertExpr captures arg
      pure (.typeof arg')
  | .unary op arg => do
      let arg' ← convertExpr captures arg
      pure (.unary op arg')
  | .binary op lhs rhs => do
      let lhs' ← convertExpr captures lhs
      let rhs' ← convertExpr captures rhs
      pure (.binary op lhs' rhs')
  | .objectLit props => do
      let props' ← props.mapM (fun (name, expr) => do
        let expr' ← convertExpr captures expr
        pure (name, expr'))
      pure (.objectLit props')
  | .arrayLit elems => do
      let elems' ← elems.mapM (convertExpr captures)
      pure (.arrayLit elems')
  | .functionDef name params body _ _ => do
      let bound := match name with
        | some n => n :: params
        | none => params
      let innerCaptures := eraseAll (freeVars body) bound
      let body' ← convertExpr innerCaptures body
      let fnName := name.getD "__lambda"
      let func : FuncDef := {
        name := fnName
        params := params
        envParam := envParamName
        body := body'
      }
      let idx ← appendFunc func
      let envVals := innerCaptures.map (convertVarRef captures)
      pure (.makeClosure idx (.makeEnv envVals))
  | .throw arg => do
      let arg' ← convertExpr captures arg
      pure (.throw arg')
  | .tryCatch body catchParam catchBody finally_ => do
      let body' ← convertExpr captures body
      let catchBody' ← convertExpr captures catchBody
      let finally' ← match finally_ with
        | some f => do
            let f' ← convertExpr captures f
            pure (some f')
        | none => pure none
      pure (.tryCatch body' catchParam catchBody' finally')
  | .while_ cond body => do
      let cond' ← convertExpr captures cond
      let body' ← convertExpr captures body
      pure (.while_ cond' body')
  | .break label => pure (.break label)
  | .continue label => pure (.continue label)
  | .return arg => do
      let arg' ← match arg with
        | some e => do
            let e' ← convertExpr captures e
            pure (some e')
        | none => pure none
      pure (.return arg')
  | .labeled label body => do
      let body' ← convertExpr captures body
      pure (.labeled label body')
  | .yield arg delegate => do
      let arg' ← match arg with
        | some e => do
            let e' ← convertExpr captures e
            pure (some e')
        | none => pure none
      pure (.yield arg' delegate)
  | .await arg => do
      let arg' ← convertExpr captures arg
      pure (.await arg')
  | .this => pure .this

partial def convertTopLevelFuncsAux (idx : Nat) : List Core.FuncDef → CCM Unit
  | [] => pure ()
  | f :: rest => do
      let body' ← convertExpr [] f.body
      let flatFunc : FuncDef := {
        name := f.name
        params := f.params
        envParam := envParamName
        body := body'
      }
      setReservedFunc idx flatFunc
      convertTopLevelFuncsAux (idx + 1) rest

def convertTopLevelFuncs (funcs : Array Core.FuncDef) : CCM Unit :=
  convertTopLevelFuncsAux 0 funcs.toList

/-- Convert a Core program to Flat by closure conversion. -/
def closureConvert (prog : Core.Program) : Except String Program := Id.run do
  let initial : CCState := { funcs := Array.replicate prog.functions.size placeholderFunc }
  let (main, st) := (do
    convertTopLevelFuncs prog.functions
    convertExpr [] prog.body).run initial
  pure (.ok { functions := st.funcs, main := main })

end VerifiedJS.Flat
