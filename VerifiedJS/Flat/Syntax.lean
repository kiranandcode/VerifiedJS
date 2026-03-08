/-
  VerifiedJS — Flat IL Syntax
  First-order: closures → structs + function indices.
-/

import VerifiedJS.Core.Syntax

namespace VerifiedJS.Flat

/-- ECMA-262 §6.2.5 language binding names reused from Core. -/
abbrev VarName := Core.VarName

/-- ECMA-262 §6.1.7 property key names reused from Core. -/
abbrev PropName := Core.PropName

/-- ECMA-262 §13.13 label names reused from Core. -/
abbrev LabelName := Core.LabelName

/-- Function index in the global function table. -/
abbrev FuncIdx := Nat

/-- Environment pointer (heap address of closure environment). -/
abbrev EnvPtr := Nat

/-- ECMA-262 §6.1 ECMAScript Language Types (Flat runtime representation). -/
inductive Value where
  | null
  | undefined
  | bool (b : Bool)
  | number (n : Float)
  | string (s : String)
  | object (addr : Nat)
  | closure (funcIdx : FuncIdx) (envPtr : EnvPtr)
  deriving Repr, BEq

/--
ECMA-262 §13 Runtime Semantics: Evaluation (first-order Flat IL).
Closure conversion eliminates nested function values into closure pairs.
-/
inductive Expr where
  | lit (v : Value)
  | var (name : VarName)
  | «let» (name : VarName) (init : Expr) (body : Expr)
  | assign (name : VarName) (value : Expr)
  | «if» (cond : Expr) (then_ : Expr) (else_ : Expr)
  | seq (a b : Expr)
  | call (funcIdx : Expr) (envPtr : Expr) (args : List Expr)
  | newObj (funcIdx : Expr) (envPtr : Expr) (args : List Expr)
  | getProp (obj : Expr) (prop : PropName)
  | setProp (obj : Expr) (prop : PropName) (value : Expr)
  | getIndex (obj : Expr) (idx : Expr)
  | setIndex (obj : Expr) (idx : Expr) (value : Expr)
  | deleteProp (obj : Expr) (prop : PropName)
  | typeof (arg : Expr)
  | getEnv (envPtr : Expr) (idx : Nat)
  | makeEnv (values : List Expr)
  | makeClosure (funcIdx : FuncIdx) (env : Expr)
  | objectLit (props : List (PropName × Expr))
  | arrayLit (elems : List Expr)
  | throw (arg : Expr)
  | tryCatch (body : Expr) (catchParam : VarName) (catchBody : Expr) (finally_ : Option Expr)
  | while_ (cond : Expr) (body : Expr)
  | «break» (label : Option LabelName)
  | «continue» (label : Option LabelName)
  | labeled (label : LabelName) (body : Expr)
  | «return» (arg : Option Expr)
  | yield (arg : Option Expr) (delegate : Bool)
  | await (arg : Expr)
  | this
  | unary (op : Core.UnaryOp) (arg : Expr)
  | binary (op : Core.BinOp) (lhs rhs : Expr)
  deriving Repr, BEq

/-- ECMA-262 §10.2 ECMAScript Function Objects (closure-converted form). -/
structure FuncDef where
  name : VarName
  params : List VarName
  envParam : VarName
  body : Expr
  deriving Repr, BEq

/-- Flat program: function table plus top-level entry expression. -/
structure Program where
  functions : Array FuncDef
  main : Expr
  deriving Repr, BEq

end VerifiedJS.Flat
