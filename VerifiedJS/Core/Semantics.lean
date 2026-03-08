/-
  VerifiedJS — Core IL Semantics
  Small-step LTS as an inductive relation.
  SPEC: §8 (Executable Code and Execution Contexts), §9 (Ordinary Object Internal Methods)
-/

import VerifiedJS.Core.Syntax

namespace VerifiedJS.Core

/-- Observable trace events emitted by Core execution. -/
inductive TraceEvent where
  | log (s : String)
  | error (s : String)
  | silent
  deriving Repr, BEq

/-- ECMA-262 §8.1 Environment Records (simplified lexical bindings for Core). -/
structure Env where
  bindings : List (VarName × Value)
  deriving Repr

/-- ECMA-262 §9.1 Ordinary object storage (heap abstract state). -/
structure Heap where
  objects : Array (List (PropName × Value))
  nextAddr : Nat
  deriving Repr

/-- ECMA-262 §8.3 Execution Contexts (Core machine state). -/
structure State where
  expr : Expr
  env : Env
  heap : Heap
  trace : List TraceEvent
  deriving Repr

/-- Empty lexical environment. -/
def Env.empty : Env :=
  { bindings := [] }

/-- Empty heap. -/
def Heap.empty : Heap :=
  { objects := #[], nextAddr := 0 }

/-- ECMA-262 §8.1.1.4 GetBindingValue (modeled as lookup in lexical bindings). -/
def Env.lookup (env : Env) (name : VarName) : Option Value :=
  match env.bindings.find? (fun kv => kv.fst == name) with
  | some kv => some kv.snd
  | none => none

private def updateBindingList (xs : List (VarName × Value)) (name : VarName) (v : Value) : List (VarName × Value) :=
  match xs with
  | [] => []
  | (n, old) :: rest =>
      if n == name then
        (n, v) :: rest
      else
        (n, old) :: updateBindingList rest name v

/-- ECMA-262 §8.1.1.4.5 SetMutableBinding (simplified update). -/
def Env.assign (env : Env) (name : VarName) (v : Value) : Env :=
  if env.bindings.any (fun kv => kv.fst == name) then
    { bindings := updateBindingList env.bindings name v }
  else
    { bindings := (name, v) :: env.bindings }

/-- ECMA-262 §8.1.1.1.2 CreateMutableBinding + §8.1.1.1.5 InitializeBinding. -/
def Env.extend (env : Env) (name : VarName) (v : Value) : Env :=
  { bindings := (name, v) :: env.bindings }

/-- Check whether an expression is a value expression. -/
def exprValue? : Expr → Option Value
  | .lit v => some v
  | _ => none

/-- ECMA-262 §7.2.14 ToBoolean (core subset). -/
def toBoolean : Value → Bool
  | .undefined => false
  | .null => false
  | .bool b => b
  | .number n => !(n == 0.0 || n.isNaN)
  | .string s => !s.isEmpty
  | .object _ => true
  | .function _ => true

/-- ECMA-262 §7.1.3 ToNumber (core subset). -/
def toNumber : Value → Float
  | .number n => n
  | .bool true => 1.0
  | .bool false => 0.0
  | .null => 0.0
  | _ => 0.0

/-- ECMA-262 §13.5 Runtime Semantics: Evaluation (core unary subset). -/
def evalUnary : UnaryOp → Value → Value
  | .neg, v => .number (-toNumber v)
  | .pos, v => .number (toNumber v)
  | .logNot, v => .bool (!toBoolean v)
  | .void, _ => .undefined
  | .bitNot, _ => .undefined

/-- ECMA-262 §13.15 Runtime Semantics: Evaluation (core binary subset). -/
def evalBinary : BinOp → Value → Value → Value
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

private def pushTrace (s : State) (t : TraceEvent) : State :=
  { s with trace := s.trace ++ [t] }

/-- One deterministic Core small-step transition with emitted trace event. -/
partial def step? (s : State) : Option (TraceEvent × State) :=
  match s.expr with
  | .lit _ => none
  | .var name =>
      match s.env.lookup name with
      | some v =>
          let s' := pushTrace { s with expr := .lit v } .silent
          some (.silent, s')
      | none =>
          let msg := "ReferenceError: " ++ name
          let s' := pushTrace { s with expr := .lit .undefined } (.error msg)
          some (.error msg, s')
  | .let name init body =>
      match exprValue? init with
      | some v =>
          let s' := pushTrace { s with expr := body, env := s.env.extend name v } .silent
          some (.silent, s')
      | none =>
          match step? { s with expr := init } with
          | some (t, si) =>
              let s' := pushTrace { s with expr := .let name si.expr body, env := si.env, heap := si.heap } t
              some (t, s')
          | none => none
  | .assign name rhs =>
      match exprValue? rhs with
      | some v =>
          let s' := pushTrace { s with expr := .lit v, env := s.env.assign name v } .silent
          some (.silent, s')
      | none =>
          match step? { s with expr := rhs } with
          | some (t, sr) =>
              let s' := pushTrace { s with expr := .assign name sr.expr, env := sr.env, heap := sr.heap } t
              some (t, s')
          | none => none
  | .if cond then_ else_ =>
      match exprValue? cond with
      | some v =>
          let next := if toBoolean v then then_ else else_
          let s' := pushTrace { s with expr := next } .silent
          some (.silent, s')
      | none =>
          match step? { s with expr := cond } with
          | some (t, sc) =>
              let s' := pushTrace { s with expr := .if sc.expr then_ else_, env := sc.env, heap := sc.heap } t
              some (t, s')
          | none => none
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
  | .unary op arg =>
      match exprValue? arg with
      | some v =>
          let s' := pushTrace { s with expr := .lit (evalUnary op v) } .silent
          some (.silent, s')
      | none =>
          match step? { s with expr := arg } with
          | some (t, sa) =>
              let s' := pushTrace { s with expr := .unary op sa.expr, env := sa.env, heap := sa.heap } t
              some (t, s')
          | none => none
  | .binary op lhs rhs =>
      match exprValue? lhs with
      | none =>
          match step? { s with expr := lhs } with
          | some (t, sl) =>
              let s' := pushTrace { s with expr := .binary op sl.expr rhs, env := sl.env, heap := sl.heap } t
              some (t, s')
          | none => none
      | some lv =>
          match exprValue? rhs with
          | none =>
              match step? { s with expr := rhs } with
              | some (t, sr) =>
                  let s' := pushTrace { s with expr := .binary op (.lit lv) sr.expr, env := sr.env, heap := sr.heap } t
                  some (t, s')
              | none => none
          | some rv =>
              let s' := pushTrace { s with expr := .lit (evalBinary op lv rv) } .silent
              some (.silent, s')
  | .while_ cond body =>
      let lowered := .if cond (.seq body (.while_ cond body)) (.lit .undefined)
      let s' := pushTrace { s with expr := lowered } .silent
      some (.silent, s')
  | .labeled _ body =>
      let s' := pushTrace { s with expr := body } .silent
      some (.silent, s')
  | .throw arg =>
      match exprValue? arg with
      | some _ =>
          let s' := pushTrace { s with expr := .lit .undefined } (.error "throw")
          some (.error "throw", s')
      | none =>
          match step? { s with expr := arg } with
          | some (t, sa) =>
              let s' := pushTrace { s with expr := .throw sa.expr, env := sa.env, heap := sa.heap } t
              some (t, s')
          | none => none
  | .this =>
      match s.env.lookup "this" with
      | some v =>
          let s' := pushTrace { s with expr := .lit v } .silent
          some (.silent, s')
      | none =>
          let s' := pushTrace { s with expr := .lit .undefined } .silent
          some (.silent, s')
  | _ =>
      let s' := pushTrace { s with expr := .lit .undefined } (.error "unimplemented core construct")
      some (.error "unimplemented core construct", s')

/-- Small-step relation induced by `step?`.
    ECMA-262 §8.3 execution context stepping. -/
inductive Step : State → TraceEvent → State → Prop where
  | mk {s : State} {t : TraceEvent} {s' : State} :
      step? s = some (t, s') →
      Step s t s'

/-- Reflexive-transitive closure of Core steps with trace accumulation. -/
inductive Steps : State → List TraceEvent → State → Prop where
  | refl (s : State) : Steps s [] s
  | tail {s1 s2 s3 : State} {t : TraceEvent} {ts : List TraceEvent} :
      Step s1 t s2 →
      Steps s2 ts s3 →
      Steps s1 (t :: ts) s3

/-- Initial Core machine state for a program body. -/
def initialState (p : Program) : State :=
  { expr := p.body, env := Env.empty, heap := Heap.empty, trace := [] }

/-- Program behavior as finite terminating trace sequence. -/
def Behaves (p : Program) (b : List TraceEvent) : Prop :=
  ∃ sFinal,
    Steps (initialState p) b sFinal ∧
    step? sFinal = none

end VerifiedJS.Core
