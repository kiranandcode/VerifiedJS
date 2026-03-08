/-
  VerifiedJS — Flat IL Semantics
-/

import VerifiedJS.Flat.Syntax
import VerifiedJS.Core.Semantics

namespace VerifiedJS.Flat

/-- ECMA-262 §8.1 Environment Records (flattened lexical environment). -/
abbrev Env := List (VarName × Value)

/-- ECMA-262 §8.3 Execution Contexts (Flat machine state). -/
structure State where
  expr : Expr
  env : Env
  heap : Core.Heap
  trace : List Core.TraceEvent
  deriving Repr

/-- Empty Flat lexical environment. -/
def Env.empty : Env := []

/-- ECMA-262 §8.1.1.4 GetBindingValue (modeled as lexical lookup). -/
def Env.lookup (env : Env) (name : VarName) : Option Value :=
  match env.find? (fun kv => kv.fst == name) with
  | some kv => some kv.snd
  | none => none

private def updateBindingList (xs : Env) (name : VarName) (v : Value) : Env :=
  match xs with
  | [] => []
  | (n, old) :: rest =>
      if n == name then
        (n, v) :: rest
      else
        (n, old) :: updateBindingList rest name v

/-- ECMA-262 §8.1.1.4.5 SetMutableBinding (simplified update). -/
def Env.assign (env : Env) (name : VarName) (v : Value) : Env :=
  if env.any (fun kv => kv.fst == name) then
    updateBindingList env name v
  else
    (name, v) :: env

/-- ECMA-262 §8.1.1.1.2 CreateMutableBinding + §8.1.1.1.5 InitializeBinding. -/
def Env.extend (env : Env) (name : VarName) (v : Value) : Env :=
  (name, v) :: env

/-- Check whether an expression is already a Flat value expression. -/
def exprValue? : Expr → Option Value
  | .lit v => some v
  | _ => none

/-- ECMA-262 §7.2.14 ToBoolean (Flat subset). -/
def toBoolean : Value → Bool
  | .undefined => false
  | .null => false
  | .bool b => b
  | .number n => !(n == 0.0 || n.isNaN)
  | .string s => !s.isEmpty
  | .object _ => true
  | .closure _ _ => true

/-- ECMA-262 §7.1.3 ToNumber (Flat subset). -/
def toNumber : Value → Float
  | .number n => n
  | .bool true => 1.0
  | .bool false => 0.0
  | .null => 0.0
  | _ => 0.0

/-- ECMA-262 §13.5 Runtime Semantics: Evaluation (Flat unary subset). -/
def evalUnary : Core.UnaryOp → Value → Value
  | .neg, v => .number (-toNumber v)
  | .pos, v => .number (toNumber v)
  | .logNot, v => .bool (!toBoolean v)
  | .void, _ => .undefined
  | .bitNot, _ => .undefined

/-- ECMA-262 §13.15 Runtime Semantics: Evaluation (Flat binary subset). -/
def evalBinary : Core.BinOp → Value → Value → Value
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

private def pushTrace (s : State) (t : Core.TraceEvent) : State :=
  { s with trace := s.trace ++ [t] }

private def allocFreshObject (h : Core.Heap) : Nat × Core.Heap :=
  let addr := h.nextAddr
  let h' : Core.Heap :=
    { objects := h.objects.push [], nextAddr := addr + 1 }
  (addr, h')

private def typeofValue : Value → Value
  | .undefined => .string "undefined"
  | .null => .string "object"
  | .bool _ => .string "boolean"
  | .number _ => .string "number"
  | .string _ => .string "string"
  | .object _ => .string "object"
  | .closure _ _ => .string "function"

private def valuesFromExprList? : List Expr → Option (List Value)
  | [] => some []
  | e :: rest =>
      match exprValue? e, valuesFromExprList? rest with
      | some v, some vs => some (v :: vs)
      | _, _ => none

/-- One deterministic Flat small-step transition with emitted trace event. -/
partial def step? (s : State) : Option (Core.TraceEvent × State) :=
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
  | .«let» name init body =>
      match exprValue? init with
      | some v =>
          let s' := pushTrace { s with expr := body, env := s.env.extend name v } .silent
          some (.silent, s')
      | none =>
          match step? { s with expr := init } with
          | some (t, si) =>
              let s' := pushTrace { s with expr := .«let» name si.expr body, env := si.env, heap := si.heap } t
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
  | .«if» cond then_ else_ =>
      match exprValue? cond with
      | some v =>
          let next := if toBoolean v then then_ else else_
          let s' := pushTrace { s with expr := next } .silent
          some (.silent, s')
      | none =>
          match step? { s with expr := cond } with
          | some (t, sc) =>
              let s' := pushTrace { s with expr := .«if» sc.expr then_ else_, env := sc.env, heap := sc.heap } t
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
                  let s' := pushTrace
                    { s with expr := .binary op (.lit lv) sr.expr, env := sr.env, heap := sr.heap } t
                  some (t, s')
              | none => none
          | some rv =>
              let s' := pushTrace { s with expr := .lit (evalBinary op lv rv) } .silent
              some (.silent, s')
  | .while_ cond body =>
      let lowered := .«if» cond (.seq body (.while_ cond body)) (.lit .undefined)
      let s' := pushTrace { s with expr := lowered } .silent
      some (.silent, s')
  | .call funcExpr envExpr args =>
      match exprValue? funcExpr with
      | none =>
          match step? { s with expr := funcExpr } with
          | some (t, sf) =>
              let s' := pushTrace
                { s with expr := .call sf.expr envExpr args, env := sf.env, heap := sf.heap } t
              some (t, s')
          | none => none
      | some _ =>
          match exprValue? envExpr with
          | none =>
              match step? { s with expr := envExpr } with
              | some (t, se) =>
                  let s' := pushTrace
                    { s with expr := .call funcExpr se.expr args, env := se.env, heap := se.heap } t
                  some (t, s')
              | none => none
          | some _ =>
              match valuesFromExprList? args with
              | some _ =>
                  let s' := pushTrace { s with expr := .lit .undefined } .silent
                  some (.silent, s')
              | none =>
                  let rec stepCallArgs (done : List Expr) (todo : List Expr) :
                      Option (Core.TraceEvent × List Expr × Env × Core.Heap) :=
                    match todo with
                    | [] => none
                    | a :: rest =>
                        match exprValue? a with
                        | some _ => stepCallArgs (done ++ [a]) rest
                        | none =>
                            match step? { s with expr := a } with
                            | some (t, sa) => some (t, done ++ (sa.expr :: rest), sa.env, sa.heap)
                            | none => none
                  match stepCallArgs [] args with
                  | some (t, args', env', heap') =>
                      let s' := pushTrace
                        { s with expr := .call funcExpr envExpr args', env := env', heap := heap' } t
                      some (t, s')
                  | none => none
  | .newObj funcExpr envExpr args =>
      match exprValue? funcExpr with
      | none =>
          match step? { s with expr := funcExpr } with
          | some (t, sf) =>
              let s' := pushTrace
                { s with expr := .newObj sf.expr envExpr args, env := sf.env, heap := sf.heap } t
              some (t, s')
          | none => none
      | some _ =>
          match exprValue? envExpr with
          | none =>
              match step? { s with expr := envExpr } with
              | some (t, se) =>
                  let s' := pushTrace
                    { s with expr := .newObj funcExpr se.expr args, env := se.env, heap := se.heap } t
                  some (t, s')
              | none => none
          | some _ =>
              match valuesFromExprList? args with
              | some _ =>
                  let (addr, heap') := allocFreshObject s.heap
                  let s' := pushTrace { s with expr := .lit (.object addr), heap := heap' } .silent
                  some (.silent, s')
              | none =>
                  let rec stepNewObjArgs (done : List Expr) (todo : List Expr) :
                      Option (Core.TraceEvent × List Expr × Env × Core.Heap) :=
                    match todo with
                    | [] => none
                    | a :: rest =>
                        match exprValue? a with
                        | some _ => stepNewObjArgs (done ++ [a]) rest
                        | none =>
                            match step? { s with expr := a } with
                            | some (t, sa) => some (t, done ++ (sa.expr :: rest), sa.env, sa.heap)
                            | none => none
                  match stepNewObjArgs [] args with
                  | some (t, args', env', heap') =>
                      let s' := pushTrace
                        { s with expr := .newObj funcExpr envExpr args', env := env', heap := heap' } t
                      some (t, s')
                  | none => none
  | .getProp obj prop =>
      match exprValue? obj with
      | some (.object _) =>
          let _ := prop
          let s' := pushTrace { s with expr := .lit .undefined } .silent
          some (.silent, s')
      | some _ =>
          let s' := pushTrace { s with expr := .lit .undefined } (.error "TypeError: getProp on non-object")
          some (.error "TypeError: getProp on non-object", s')
      | none =>
          match step? { s with expr := obj } with
          | some (t, so) =>
              let s' := pushTrace { s with expr := .getProp so.expr prop, env := so.env, heap := so.heap } t
              some (t, s')
          | none => none
  | .setProp obj prop value =>
      match exprValue? obj with
      | none =>
          match step? { s with expr := obj } with
          | some (t, so) =>
              let s' := pushTrace { s with expr := .setProp so.expr prop value, env := so.env, heap := so.heap } t
              some (t, s')
          | none => none
      | some (.object _) =>
          match exprValue? value with
          | some v =>
              let _ := prop
              let s' := pushTrace { s with expr := .lit v } .silent
              some (.silent, s')
          | none =>
              match step? { s with expr := value } with
              | some (t, sv) =>
                  let s' := pushTrace
                    { s with expr := .setProp obj prop sv.expr, env := sv.env, heap := sv.heap } t
                  some (t, s')
              | none => none
      | some _ =>
          let s' := pushTrace { s with expr := .lit .undefined } (.error "TypeError: setProp on non-object")
          some (.error "TypeError: setProp on non-object", s')
  | .getIndex obj idx =>
      match exprValue? obj with
      | none =>
          match step? { s with expr := obj } with
          | some (t, so) =>
              let s' := pushTrace { s with expr := .getIndex so.expr idx, env := so.env, heap := so.heap } t
              some (t, s')
          | none => none
      | some (.object _) =>
          match exprValue? idx with
          | some _ =>
              let s' := pushTrace { s with expr := .lit .undefined } .silent
              some (.silent, s')
          | none =>
              match step? { s with expr := idx } with
              | some (t, si) =>
                  let s' := pushTrace { s with expr := .getIndex obj si.expr, env := si.env, heap := si.heap } t
                  some (t, s')
              | none => none
      | some _ =>
          let s' := pushTrace { s with expr := .lit .undefined } (.error "TypeError: getIndex on non-object")
          some (.error "TypeError: getIndex on non-object", s')
  | .setIndex obj idx value =>
      match exprValue? obj with
      | none =>
          match step? { s with expr := obj } with
          | some (t, so) =>
              let s' := pushTrace { s with expr := .setIndex so.expr idx value, env := so.env, heap := so.heap } t
              some (t, s')
          | none => none
      | some (.object _) =>
          match exprValue? idx with
          | none =>
              match step? { s with expr := idx } with
              | some (t, si) =>
                  let s' := pushTrace
                    { s with expr := .setIndex obj si.expr value, env := si.env, heap := si.heap } t
                  some (t, s')
              | none => none
          | some _ =>
              match exprValue? value with
              | some v =>
                  let s' := pushTrace { s with expr := .lit v } .silent
                  some (.silent, s')
              | none =>
                  match step? { s with expr := value } with
                  | some (t, sv) =>
                      let s' := pushTrace
                        { s with expr := .setIndex obj idx sv.expr, env := sv.env, heap := sv.heap } t
                      some (t, s')
                  | none => none
      | some _ =>
          let s' := pushTrace { s with expr := .lit .undefined } (.error "TypeError: setIndex on non-object")
          some (.error "TypeError: setIndex on non-object", s')
  | .deleteProp obj prop =>
      match exprValue? obj with
      | some (.object _) =>
          let _ := prop
          let s' := pushTrace { s with expr := .lit (.bool true) } .silent
          some (.silent, s')
      | some _ =>
          let s' := pushTrace { s with expr := .lit (.bool true) } .silent
          some (.silent, s')
      | none =>
          match step? { s with expr := obj } with
          | some (t, so) =>
              let s' := pushTrace { s with expr := .deleteProp so.expr prop, env := so.env, heap := so.heap } t
              some (t, s')
          | none => none
  | .typeof arg =>
      match exprValue? arg with
      | some v =>
          let s' := pushTrace { s with expr := .lit (typeofValue v) } .silent
          some (.silent, s')
      | none =>
          match step? { s with expr := arg } with
          | some (t, sa) =>
              let s' := pushTrace { s with expr := .typeof sa.expr, env := sa.env, heap := sa.heap } t
              some (t, s')
          | none => none
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
  | .makeClosure idx envExpr =>
      match exprValue? envExpr with
      | some (.object envPtr) =>
          let s' := pushTrace { s with expr := .lit (.closure idx envPtr) } .silent
          some (.silent, s')
      | some _ =>
          let s' := pushTrace { s with expr := .lit .undefined } (.error "TypeError: invalid closure environment")
          some (.error "TypeError: invalid closure environment", s')
      | none =>
          match step? { s with expr := envExpr } with
          | some (t, se) =>
              let s' := pushTrace { s with expr := .makeClosure idx se.expr, env := se.env, heap := se.heap } t
              some (t, s')
          | none => none
  | .getEnv envExpr idx =>
      match exprValue? envExpr with
      | some (.object _) =>
          let key := "__env" ++ toString idx
          let msg := "unimplemented flat env lookup for key " ++ key
          let s' := pushTrace { s with expr := .lit .undefined } (.error msg)
          some (.error msg, s')
      | some _ =>
          let s' := pushTrace { s with expr := .lit .undefined } (.error "TypeError: invalid env pointer")
          some (.error "TypeError: invalid env pointer", s')
      | none =>
          match step? { s with expr := envExpr } with
          | some (t, se) =>
              let s' := pushTrace { s with expr := .getEnv se.expr idx, env := se.env, heap := se.heap } t
              some (t, s')
          | none => none
  | .makeEnv values =>
      match valuesFromExprList? values with
      | some _ =>
          let (addr, heap') := allocFreshObject s.heap
          let s' := pushTrace { s with expr := .lit (.object addr), heap := heap' } .silent
          some (.silent, s')
      | none =>
          let rec stepValues (done : List Expr) (todo : List Expr) :
              Option (Core.TraceEvent × List Expr × Env × Core.Heap) :=
            match todo with
            | [] => none
            | e :: rest =>
                match exprValue? e with
                | some _ => stepValues (done ++ [e]) rest
                | none =>
                    match step? { s with expr := e } with
                    | some (t, se) => some (t, done ++ (se.expr :: rest), se.env, se.heap)
                    | none => none
          match stepValues [] values with
          | some (t, values', env', heap') =>
              let s' := pushTrace { s with expr := .makeEnv values', env := env', heap := heap' } t
              some (t, s')
          | none => none
  | .objectLit props =>
      let vals := props.map Prod.snd
      match valuesFromExprList? vals with
      | some _ =>
          let (addr, heap') := allocFreshObject s.heap
          let s' := pushTrace { s with expr := .lit (.object addr), heap := heap' } .silent
          some (.silent, s')
      | none =>
          let rec stepProps (done : List (PropName × Expr)) (todo : List (PropName × Expr)) :
              Option (Core.TraceEvent × List (PropName × Expr) × Env × Core.Heap) :=
            match todo with
            | [] => none
            | (name, e) :: rest =>
                match exprValue? e with
                | some _ => stepProps (done ++ [(name, e)]) rest
                | none =>
                    match step? { s with expr := e } with
                    | some (t, se) => some (t, done ++ ((name, se.expr) :: rest), se.env, se.heap)
                    | none => none
          match stepProps [] props with
          | some (t, props', env', heap') =>
              let s' := pushTrace { s with expr := .objectLit props', env := env', heap := heap' } t
              some (t, s')
          | none => none
  | .arrayLit elems =>
      match valuesFromExprList? elems with
      | some _ =>
          let (addr, heap') := allocFreshObject s.heap
          let s' := pushTrace { s with expr := .lit (.object addr), heap := heap' } .silent
          some (.silent, s')
      | none =>
          let rec stepElems (done : List Expr) (todo : List Expr) :
              Option (Core.TraceEvent × List Expr × Env × Core.Heap) :=
            match todo with
            | [] => none
            | e :: rest =>
                match exprValue? e with
                | some _ => stepElems (done ++ [e]) rest
                | none =>
                    match step? { s with expr := e } with
                    | some (t, se) => some (t, done ++ (se.expr :: rest), se.env, se.heap)
                    | none => none
          match stepElems [] elems with
          | some (t, elems', env', heap') =>
              let s' := pushTrace { s with expr := .arrayLit elems', env := env', heap := heap' } t
              some (t, s')
          | none => none
  | .tryCatch body catchParam catchBody finally_ =>
      match exprValue? body with
      | some v =>
          match finally_ with
          | some fin =>
              let s' := pushTrace { s with expr := .seq fin (.lit v) } .silent
              some (.silent, s')
          | none =>
              let s' := pushTrace { s with expr := .lit v } .silent
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
  | .«break» label =>
      let l := label.getD ""
      let msg := "break:" ++ l
      let s' := pushTrace { s with expr := .lit .undefined } (.error msg)
      some (.error msg, s')
  | .«continue» label =>
      let l := label.getD ""
      let msg := "continue:" ++ l
      let s' := pushTrace { s with expr := .lit .undefined } (.error msg)
      some (.error msg, s')
  | .«return» arg =>
      match arg with
      | none =>
          let s' := pushTrace { s with expr := .lit .undefined } .silent
          some (.silent, s')
      | some e =>
          match exprValue? e with
          | some v =>
              let s' := pushTrace { s with expr := .lit v } .silent
              some (.silent, s')
          | none =>
              match step? { s with expr := e } with
              | some (t, se) =>
                  let s' := pushTrace { s with expr := .«return» (some se.expr), env := se.env, heap := se.heap } t
                  some (t, s')
              | none => none
  | .yield arg delegate =>
      match arg with
      | none =>
          let s' := pushTrace { s with expr := .lit .undefined } .silent
          some (.silent, s')
      | some e =>
          match exprValue? e with
          | some v =>
              let s' := pushTrace { s with expr := .lit v } .silent
              some (.silent, s')
          | none =>
              match step? { s with expr := e } with
              | some (t, se) =>
                  let s' := pushTrace
                    { s with expr := .yield (some se.expr) delegate, env := se.env, heap := se.heap } t
                  some (t, s')
              | none => none
  | .await arg =>
      match exprValue? arg with
      | some v =>
          let s' := pushTrace { s with expr := .lit v } .silent
          some (.silent, s')
      | none =>
          match step? { s with expr := arg } with
          | some (t, sa) =>
              let s' := pushTrace { s with expr := .await sa.expr, env := sa.env, heap := sa.heap } t
              some (t, s')
          | none => none

/-- Small-step relation induced by `step?`.
    ECMA-262 §8.3 execution context stepping. -/
inductive Step : State → Core.TraceEvent → State → Prop where
  | mk {s : State} {t : Core.TraceEvent} {s' : State} :
      step? s = some (t, s') →
      Step s t s'

/-- Reflexive-transitive closure of Flat steps with trace accumulation. -/
inductive Steps : State → List Core.TraceEvent → State → Prop where
  | refl (s : State) : Steps s [] s
  | tail {s1 s2 s3 : State} {t : Core.TraceEvent} {ts : List Core.TraceEvent} :
      Step s1 t s2 →
      Steps s2 ts s3 →
      Steps s1 (t :: ts) s3

/-- Initial Flat machine state for a program entry expression. -/
def initialState (p : Program) : State :=
  { expr := p.main, env := Env.empty, heap := Core.Heap.empty, trace := [] }

/-- Behavioral semantics -/
def Behaves (p : Program) (b : List Core.TraceEvent) : Prop :=
  ∃ s', Steps (initialState p) b s' ∧ step? s' = none

end VerifiedJS.Flat
