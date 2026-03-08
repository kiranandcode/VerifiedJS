/-
  VerifiedJS — ANF IL Semantics
  Small-step LTS as an inductive relation.
  SPEC: ECMA-262 §8 (Execution Contexts), §13 (Runtime Semantics: Evaluation)
-/

import VerifiedJS.ANF.Syntax
import VerifiedJS.Flat.Syntax
import VerifiedJS.Core.Semantics

namespace VerifiedJS.ANF

/-- ECMA-262 §8.1 Environment Records (flattened lexical environment for ANF). -/
abbrev Env := List (VarName × Flat.Value)

/-- ECMA-262 §8.3 Execution Contexts (ANF machine state). -/
structure State where
  expr : Expr
  env : Env
  heap : Core.Heap
  trace : List Core.TraceEvent
  deriving Repr

/-- Empty ANF lexical environment. -/
def Env.empty : Env := []

/-- ECMA-262 §8.1.1.4 GetBindingValue (modeled as lexical lookup). -/
def Env.lookup (env : Env) (name : VarName) : Option Flat.Value :=
  match env.find? (fun kv => kv.fst == name) with
  | some kv => some kv.snd
  | none => none

private def updateBindingList (xs : Env) (name : VarName) (v : Flat.Value) : Env :=
  match xs with
  | [] => []
  | (n, old) :: rest =>
      if n == name then
        (n, v) :: rest
      else
        (n, old) :: updateBindingList rest name v

/-- ECMA-262 §8.1.1.4.5 SetMutableBinding (simplified update). -/
def Env.assign (env : Env) (name : VarName) (v : Flat.Value) : Env :=
  if env.any (fun kv => kv.fst == name) then
    updateBindingList env name v
  else
    (name, v) :: env

/-- ECMA-262 §8.1.1.1.2 CreateMutableBinding + §8.1.1.1.5 InitializeBinding. -/
def Env.extend (env : Env) (name : VarName) (v : Flat.Value) : Env :=
  (name, v) :: env

private def pushTrace (s : State) (t : Core.TraceEvent) : State :=
  { s with trace := s.trace ++ [t] }

/-- Convert an ANF literal-like trivial to a Flat value when possible. -/
def trivialValue? : Trivial → Option Flat.Value
  | .var _ => none
  | .litNull => some .null
  | .litUndefined => some .undefined
  | .litBool b => some (.bool b)
  | .litNum n => some (.number n)
  | .litStr s => some (.string s)
  | .litObject addr => some (.object addr)
  | .litClosure funcIdx envPtr => some (.closure funcIdx envPtr)

private def trivialOfValue : Flat.Value → Trivial
  | .null => .litNull
  | .undefined => .litUndefined
  | .bool b => .litBool b
  | .number n => .litNum n
  | .string s => .litStr s
  | .object addr => .litObject addr
  | .closure funcIdx envPtr => .litClosure funcIdx envPtr

/-- Evaluate a trivial in the current environment (variables may fail with ReferenceError). -/
def evalTrivial (env : Env) : Trivial → Except String Flat.Value
  | .var name =>
      match env.lookup name with
      | some v => .ok v
      | none => .error s!"ReferenceError: {name}"
  | t =>
      match trivialValue? t with
      | some v => .ok v
      | none => .error "TypeError: invalid trivial"

private def evalTrivialList (env : Env) (ts : List Trivial) : Except String (List Flat.Value) :=
  ts.mapM (evalTrivial env)

private def toBoolean : Flat.Value → Bool
  | .undefined => false
  | .null => false
  | .bool b => b
  | .number n => !(n == 0.0 || n.isNaN)
  | .string s => !s.isEmpty
  | .object _ => true
  | .closure _ _ => true

private def toNumber : Flat.Value → Float
  | .number n => n
  | .bool true => 1.0
  | .bool false => 0.0
  | .null => 0.0
  | _ => 0.0

private def evalUnary : Core.UnaryOp → Flat.Value → Flat.Value
  | .neg, v => .number (-toNumber v)
  | .pos, v => .number (toNumber v)
  | .logNot, v => .bool (!toBoolean v)
  | .void, _ => .undefined
  | .bitNot, _ => .undefined

private def evalBinary : Core.BinOp → Flat.Value → Flat.Value → Flat.Value
  | .add, .string a, .string b => .string (a ++ b)
  | .add, a, b => .number (toNumber a + toNumber b)
  | .sub, a, b => .number (toNumber a - toNumber b)
  | .mul, a, b => .number (toNumber a * toNumber b)
  | .div, a, b => .number (toNumber a / toNumber b)
  | .eq, a, b => .bool (a == b)
  | .neq, a, b => .bool (a != b)
  | .strictEq, a, b => .bool (a == b)
  | .strictNeq, a, b => .bool (a != b)
  | .lt, a, b => .bool (toNumber a < toNumber b)
  | .gt, a, b => .bool (toNumber a > toNumber b)
  | .le, a, b => .bool (toNumber a <= toNumber b)
  | .ge, a, b => .bool (toNumber a >= toNumber b)
  | .logAnd, a, b => if toBoolean a then b else a
  | .logOr, a, b => if toBoolean a then a else b
  | _, _, _ => .undefined

private def flatToCoreValue : Flat.Value → Core.Value
  | .null => .null
  | .undefined => .undefined
  | .bool b => .bool b
  | .number n => .number n
  | .string s => .string s
  | .object addr => .object addr
  | .closure funcIdx _ => .function funcIdx

private def coreToFlatValue : Core.Value → Flat.Value
  | .null => .null
  | .undefined => .undefined
  | .bool b => .bool b
  | .number n => .number n
  | .string s => .string s
  | .object addr => .object addr
  | .function idx => .closure idx 0

private def envSlotKey (idx : Nat) : PropName :=
  "__env" ++ toString idx

private def encodeEnvPropsAux (idx : Nat) (values : List Flat.Value) : List (PropName × Core.Value) :=
  match values with
  | [] => []
  | v :: rest => (envSlotKey idx, flatToCoreValue v) :: encodeEnvPropsAux (idx + 1) rest

private def encodeEnvProps (values : List Flat.Value) : List (PropName × Core.Value) :=
  encodeEnvPropsAux 0 values

private def allocFreshObject (h : Core.Heap) : Nat × Core.Heap :=
  let addr := h.nextAddr
  let h' : Core.Heap := { objects := h.objects.push [], nextAddr := addr + 1 }
  (addr, h')

private def allocEnvObject (h : Core.Heap) (values : List Flat.Value) : Nat × Core.Heap :=
  let addr := h.nextAddr
  let h' : Core.Heap := { objects := h.objects.push (encodeEnvProps values), nextAddr := addr + 1 }
  (addr, h')

private def heapObjectAt? (h : Core.Heap) (addr : Nat) : Option (List (Core.PropName × Core.Value)) :=
  if hAddr : addr < h.objects.size then
    let _ := hAddr
    some (h.objects[addr]!)
  else
    none

private def typeofValue : Flat.Value → Flat.Value
  | .undefined => .string "undefined"
  | .null => .string "object"
  | .bool _ => .string "boolean"
  | .number _ => .string "number"
  | .string _ => .string "string"
  | .object _ => .string "object"
  | .closure _ _ => .string "function"

private structure ComplexResult where
  event : Core.TraceEvent
  env : Env
  heap : Core.Heap
  value : Flat.Value

private def mkError (msg : String) (s : State) : ComplexResult :=
  { event := .error msg, env := s.env, heap := s.heap, value := .undefined }

/-- Evaluate one ANF complex expression atomically. -/
def evalComplex (s : State) (rhs : ComplexExpr) : ComplexResult :=
  match rhs with
  | .trivial t =>
      match evalTrivial s.env t with
      | .ok v => { event := .silent, env := s.env, heap := s.heap, value := v }
      | .error msg => mkError msg s
  | .assign name value =>
      match evalTrivial s.env value with
      | .ok v => { event := .silent, env := s.env.assign name v, heap := s.heap, value := v }
      | .error msg => mkError msg s
  | .call callee env args =>
      match evalTrivial s.env callee, evalTrivial s.env env, evalTrivialList s.env args with
      | .ok _, .ok _, .ok _ => { event := .silent, env := s.env, heap := s.heap, value := .undefined }
      | .error msg, _, _ => mkError msg s
      | _, .error msg, _ => mkError msg s
      | _, _, .error msg => mkError msg s
  | .newObj callee env args =>
      match evalTrivial s.env callee, evalTrivial s.env env, evalTrivialList s.env args with
      | .ok _, .ok _, .ok _ =>
          let (addr, heap') := allocFreshObject s.heap
          { event := .silent, env := s.env, heap := heap', value := .object addr }
      | .error msg, _, _ => mkError msg s
      | _, .error msg, _ => mkError msg s
      | _, _, .error msg => mkError msg s
  | .getProp obj _prop =>
      match evalTrivial s.env obj with
      | .ok (.object _) => { event := .silent, env := s.env, heap := s.heap, value := .undefined }
      | .ok _ => mkError "TypeError: getProp on non-object" s
      | .error msg => mkError msg s
  | .setProp obj _prop value =>
      match evalTrivial s.env obj, evalTrivial s.env value with
      | .ok (.object _), .ok v => { event := .silent, env := s.env, heap := s.heap, value := v }
      | .ok (.object _), .error msg => mkError msg s
      | .ok _, _ => mkError "TypeError: setProp on non-object" s
      | .error msg, _ => mkError msg s
  | .getIndex obj idx =>
      match evalTrivial s.env obj, evalTrivial s.env idx with
      | .ok (.object _), .ok _ => { event := .silent, env := s.env, heap := s.heap, value := .undefined }
      | .ok (.object _), .error msg => mkError msg s
      | .ok _, _ => mkError "TypeError: getIndex on non-object" s
      | .error msg, _ => mkError msg s
  | .setIndex obj idx value =>
      match evalTrivial s.env obj, evalTrivial s.env idx, evalTrivial s.env value with
      | .ok (.object _), .ok _, .ok v => { event := .silent, env := s.env, heap := s.heap, value := v }
      | .ok (.object _), .error msg, _ => mkError msg s
      | .ok (.object _), _, .error msg => mkError msg s
      | .ok _, _, _ => mkError "TypeError: setIndex on non-object" s
      | .error msg, _, _ => mkError msg s
  | .deleteProp obj _prop =>
      match evalTrivial s.env obj with
      | .ok _ => { event := .silent, env := s.env, heap := s.heap, value := .bool true }
      | .error msg => mkError msg s
  | .typeof arg =>
      match evalTrivial s.env arg with
      | .ok v => { event := .silent, env := s.env, heap := s.heap, value := typeofValue v }
      | .error _ =>
          -- typeof undeclared identifiers does not throw in JavaScript.
          { event := .silent, env := s.env, heap := s.heap, value := .string "undefined" }
  | .getEnv envTriv idx =>
      match evalTrivial s.env envTriv with
      | .ok (.object envPtr) =>
          match heapObjectAt? s.heap envPtr with
          | some props =>
              let key := envSlotKey idx
              match props.find? (fun kv => kv.fst == key) with
              | some kv =>
                  { event := .silent, env := s.env, heap := s.heap, value := coreToFlatValue kv.snd }
              | none => mkError s!"ReferenceError: missing env slot {key}" s
          | none => mkError s!"TypeError: dangling env pointer {envPtr}" s
      | .ok _ => mkError "TypeError: invalid env pointer" s
      | .error msg => mkError msg s
  | .makeEnv values =>
      match evalTrivialList s.env values with
      | .ok captured =>
          let (addr, heap') := allocEnvObject s.heap captured
          { event := .silent, env := s.env, heap := heap', value := .object addr }
      | .error msg => mkError msg s
  | .makeClosure funcIdx env =>
      match evalTrivial s.env env with
      | .ok (.object envPtr) => { event := .silent, env := s.env, heap := s.heap, value := .closure funcIdx envPtr }
      | .ok _ => mkError "TypeError: invalid closure environment" s
      | .error msg => mkError msg s
  | .objectLit props =>
      match props.mapM (fun (_, t) => evalTrivial s.env t) with
      | .ok _ =>
          let (addr, heap') := allocFreshObject s.heap
          { event := .silent, env := s.env, heap := heap', value := .object addr }
      | .error msg => mkError msg s
  | .arrayLit elems =>
      match evalTrivialList s.env elems with
      | .ok _ =>
          let (addr, heap') := allocFreshObject s.heap
          { event := .silent, env := s.env, heap := heap', value := .object addr }
      | .error msg => mkError msg s
  | .unary op arg =>
      match evalTrivial s.env arg with
      | .ok v => { event := .silent, env := s.env, heap := s.heap, value := evalUnary op v }
      | .error msg => mkError msg s
  | .binary op lhs rhs =>
      match evalTrivial s.env lhs, evalTrivial s.env rhs with
      | .ok lv, .ok rv => { event := .silent, env := s.env, heap := s.heap, value := evalBinary op lv rv }
      | .error msg, _ => mkError msg s
      | _, .error msg => mkError msg s

/-- Check whether an ANF expression is already a value expression. -/
def exprValue? : Expr → Option Flat.Value
  | .trivial t => trivialValue? t
  | _ => none

/-- One deterministic ANF small-step transition with emitted trace event. -/
partial def step? (s : State) : Option (Core.TraceEvent × State) :=
  match s.expr with
  | .trivial t =>
      match t with
      | .var name =>
          match s.env.lookup name with
          | some v =>
              let s' := pushTrace { s with expr := .trivial (trivialOfValue v) } .silent
              some (.silent, s')
          | none =>
              let msg := s!"ReferenceError: {name}"
              let s' := pushTrace { s with expr := .trivial .litUndefined } (.error msg)
              some (.error msg, s')
      | _ =>
          -- Literal trivials are final values in ANF and do not step further.
          none
  | .«let» name rhs body =>
      let r := evalComplex s rhs
      let s' := pushTrace { s with expr := body, env := r.env.extend name r.value, heap := r.heap } r.event
      some (r.event, s')
  | .seq a b =>
      match exprValue? a with
      | some _ =>
          let s' := pushTrace { s with expr := b } .silent
          some (.silent, s')
      | none =>
          match step? { s with expr := a } with
          | some (t, sa) =>
              let s' := pushTrace { s with expr := .seq sa.expr b, env := sa.env, heap := sa.heap } t
              some (t, s')
          | none => none
  | .«if» cond then_ else_ =>
      match evalTrivial s.env cond with
      | .ok v =>
          let next := if toBoolean v then then_ else else_
          let s' := pushTrace { s with expr := next } .silent
          some (.silent, s')
      | .error msg =>
          let s' := pushTrace { s with expr := .trivial .litUndefined } (.error msg)
          some (.error msg, s')
  | .while_ cond body =>
      match exprValue? cond with
      | some v =>
          let next := if toBoolean v then .seq body (.while_ cond body) else .trivial .litUndefined
          let s' := pushTrace { s with expr := next } .silent
          some (.silent, s')
      | none =>
          match step? { s with expr := cond } with
          | some (t, sc) =>
              let s' := pushTrace { s with expr := .while_ sc.expr body, env := sc.env, heap := sc.heap } t
              some (t, s')
          | none => none
  | .throw arg =>
      match evalTrivial s.env arg with
      | .ok _ =>
          let s' := pushTrace { s with expr := .trivial .litUndefined } (.error "throw")
          some (.error "throw", s')
      | .error msg =>
          let s' := pushTrace { s with expr := .trivial .litUndefined } (.error msg)
          some (.error msg, s')
  | .tryCatch body catchParam catchBody finally_ =>
      match exprValue? body with
      | some v =>
          match finally_ with
          | some fin =>
              let s' := pushTrace { s with expr := .seq fin (.trivial (trivialOfValue v)) } .silent
              some (.silent, s')
          | none =>
              let s' := pushTrace { s with expr := .trivial (trivialOfValue v) } .silent
              some (.silent, s')
      | none =>
          match step? { s with expr := body } with
          | some (.error msg, sb) =>
              let handler :=
                match finally_ with
                | some fin => .seq catchBody fin
                | none => catchBody
              let s' := pushTrace
                { s with expr := handler, env := sb.env.extend catchParam (.string msg), heap := sb.heap } (.error msg)
              some (.error msg, s')
          | some (t, sb) =>
              let s' := pushTrace
                { s with expr := .tryCatch sb.expr catchParam catchBody finally_, env := sb.env, heap := sb.heap } t
              some (t, s')
          | none => none
  | .«return» arg =>
      match arg with
      | none =>
          let s' := pushTrace { s with expr := .trivial .litUndefined } .silent
          some (.silent, s')
      | some t =>
          match evalTrivial s.env t with
          | .ok v =>
              let s' := pushTrace { s with expr := .trivial (trivialOfValue v) } .silent
              some (.silent, s')
          | .error msg =>
              let s' := pushTrace { s with expr := .trivial .litUndefined } (.error msg)
              some (.error msg, s')
  | .yield arg delegate =>
      let _ := delegate
      match arg with
      | none =>
          let s' := pushTrace { s with expr := .trivial .litUndefined } .silent
          some (.silent, s')
      | some t =>
          match evalTrivial s.env t with
          | .ok v =>
              let s' := pushTrace { s with expr := .trivial (trivialOfValue v) } .silent
              some (.silent, s')
          | .error msg =>
              let s' := pushTrace { s with expr := .trivial .litUndefined } (.error msg)
              some (.error msg, s')
  | .await arg =>
      match evalTrivial s.env arg with
      | .ok v =>
          let s' := pushTrace { s with expr := .trivial (trivialOfValue v) } .silent
          some (.silent, s')
      | .error msg =>
          let s' := pushTrace { s with expr := .trivial .litUndefined } (.error msg)
          some (.error msg, s')
  | .labeled _ body =>
      let s' := pushTrace { s with expr := body } .silent
      some (.silent, s')
  | .«break» label =>
      let l := label.getD ""
      let msg := "break:" ++ l
      let s' := pushTrace { s with expr := .trivial .litUndefined } (.error msg)
      some (.error msg, s')
  | .«continue» label =>
      let l := label.getD ""
      let msg := "continue:" ++ l
      let s' := pushTrace { s with expr := .trivial .litUndefined } (.error msg)
      some (.error msg, s')

/-- Small-step relation induced by `step?`. -/
inductive Step : State → Core.TraceEvent → State → Prop where
  | mk {s : State} {t : Core.TraceEvent} {s' : State} :
      step? s = some (t, s') →
      Step s t s'

/-- Reflexive-transitive closure of ANF steps with trace accumulation. -/
inductive Steps : State → List Core.TraceEvent → State → Prop where
  | refl (s : State) : Steps s [] s
  | tail {s1 s2 s3 : State} {t : Core.TraceEvent} {ts : List Core.TraceEvent} :
      Step s1 t s2 →
      Steps s2 ts s3 →
      Steps s1 (t :: ts) s3

/-- Initial ANF machine state for a program entry expression. -/
def initialState (p : Program) : State :=
  { expr := p.main, env := Env.empty, heap := Core.Heap.empty, trace := [] }

/-- Program behavior as finite terminating trace sequence. -/
def Behaves (p : Program) (b : List Core.TraceEvent) : Prop :=
  ∃ sFinal,
    Steps (initialState p) b sFinal ∧
    step? sFinal = none

end VerifiedJS.ANF
