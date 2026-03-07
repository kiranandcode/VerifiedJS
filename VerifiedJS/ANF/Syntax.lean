/-
  VerifiedJS — ANF IL Syntax
  A-normal form: all non-trivial computations are named and sequenced.
  SPEC: expression/statement runtime behavior follows ECMA-262 §13.
-/

import VerifiedJS.Core.Syntax

namespace VerifiedJS.ANF

/-- Local variable names in ANF programs. -/
abbrev VarName := String

/-- Object property names in ANF programs. -/
abbrev PropName := String

/-- Function index in the global function table after closure conversion. -/
abbrev FuncIdx := Nat

/-- Environment slot index in closure environments. -/
abbrev EnvSlot := Nat

/-- ANF trivial values: side-effect-free atoms that can be used directly. -/
inductive Trivial where
  | var (name : VarName)
  | litNull
  | litUndefined
  | litBool (b : Bool)
  | litNum (n : Float)
  | litStr (s : String)
  deriving Repr, BEq

mutual

/-- ANF computation terms: control-flow and sequencing around let-bound computations. -/
inductive Expr where
  | trivial (t : Trivial)
  | «let» (name : VarName) (rhs : ComplexExpr) (body : Expr)
  | seq (a b : Expr)
  | «if» (cond : Trivial) (then_ : Expr) (else_ : Expr)
  | while_ (cond : Expr) (body : Expr)
  | throw (arg : Trivial)
  | tryCatch (body : Expr) (catchParam : VarName) (catchBody : Expr) (finally_ : Option Expr)
  | «return» (arg : Option Trivial)
  | labeled (label : String) (body : Expr)
  | «break» (label : Option String)
  | «continue» (label : Option String)
  deriving Repr, BEq

/-- ANF complex expressions: primitive computations whose operands are trivial. -/
inductive ComplexExpr where
  | trivial (t : Trivial)
  | assign (name : VarName) (value : Trivial)
  | call (callee : Trivial) (env : Trivial) (args : List Trivial)
  | getProp (obj : Trivial) (prop : PropName)
  | setProp (obj : Trivial) (prop : PropName) (value : Trivial)
  | getEnv (env : Trivial) (idx : EnvSlot)
  | makeEnv (values : List Trivial)
  | makeClosure (funcIdx : FuncIdx) (env : Trivial)
  | objectLit (props : List (PropName × Trivial))
  | arrayLit (elems : List Trivial)
  | unary (op : Core.UnaryOp) (arg : Trivial)
  | binary (op : Core.BinOp) (lhs rhs : Trivial)
  deriving Repr, BEq

end

/-- ANF function definition. -/
structure FuncDef where
  name : String
  params : List VarName
  envParam : VarName
  body : Expr
  deriving Repr, BEq

/-- ANF program. -/
structure Program where
  functions : Array FuncDef
  main : Expr
  deriving Repr, BEq

end VerifiedJS.ANF
