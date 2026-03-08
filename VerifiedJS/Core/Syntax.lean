/-
  VerifiedJS — Core IL Syntax
  Desugared subset: destructuring/for-in/classes → primitives.
  SPEC: Desugared form of §8 (Executable Code), §9 (Ordinary Objects)
-/

namespace VerifiedJS.Core

/-- ECMA-262 §6.1 language values in Core. -/
abbrev VarName := String

/-- ECMA-262 §6.1.7 property keys (string-normalized in Core). -/
abbrev PropName := String

/-- ECMA-262 §13.13 Labels (used by break/continue). -/
abbrev LabelName := String

/-- ECMA-262 §10.2 function identity (global function table index in Core). -/
abbrev FuncIdx := Nat

/-- ECMA-262 §13.5, §13.4, §13.5 Runtime Semantics: unary operators. -/
inductive UnaryOp where
  | neg | pos | bitNot | logNot | void
  deriving Repr, BEq

/-- ECMA-262 §13.8-§13.11, §13.15 Runtime Semantics: binary operators. -/
inductive BinOp where
  | add | sub | mul | div | mod | exp
  | eq | neq | strictEq | strictNeq
  | lt | gt | le | ge
  | bitAnd | bitOr | bitXor | shl | shr | ushr
  | logAnd | logOr
  | instanceof | «in»
  deriving Repr, BEq

/-- ECMA-262 §6.1 language values after Core desugaring. -/
inductive Value where
  | null
  | undefined
  | bool (b : Bool)
  | number (n : Float)
  | string (s : String)
  | object (addr : Nat) -- heap address
  | function (idx : FuncIdx) -- function table index
  deriving Repr, BEq

/--
ECMA-262 §13 Runtime Semantics: Evaluation (desugared Core expression language).
Control forms and effects are expression-based to simplify small-step semantics.
-/
inductive Expr where
  | lit (v : Value)
  | var (name : VarName)
  | «let» (name : VarName) (init : Expr) (body : Expr)
  | assign (name : VarName) (value : Expr)
  | «if» (cond : Expr) (then_ : Expr) (else_ : Expr)
  | seq (a b : Expr)
  | call (callee : Expr) (args : List Expr)
  | newObj (callee : Expr) (args : List Expr)
  | getProp (obj : Expr) (prop : PropName)
  | setProp (obj : Expr) (prop : PropName) (value : Expr)
  | getIndex (obj : Expr) (idx : Expr)
  | setIndex (obj : Expr) (idx : Expr) (value : Expr)
  | deleteProp (obj : Expr) (prop : PropName)
  | typeof (arg : Expr)
  | unary (op : UnaryOp) (arg : Expr)
  | binary (op : BinOp) (lhs rhs : Expr)
  | objectLit (props : List (PropName × Expr))
  | arrayLit (elems : List Expr)
  | functionDef (name : Option VarName) (params : List VarName) (body : Expr)
    (isAsync : Bool) (isGenerator : Bool)
  | throw (arg : Expr)
  | tryCatch (body : Expr) (catchParam : VarName) (catchBody : Expr) (finally_ : Option Expr)
  | while_ (cond : Expr) (body : Expr)
  | «break» (label : Option LabelName)
  | «continue» (label : Option LabelName)
  | «return» (arg : Option Expr)
  | labeled (label : LabelName) (body : Expr)
  | yield (arg : Option Expr) (delegate : Bool)
  | await (arg : Expr)
  | this
  deriving Repr, BEq

/-- ECMA-262 §10.2 function metadata captured in Core programs. -/
structure FuncDef where
  name : VarName
  params : List VarName
  body : Expr
  isAsync : Bool := false
  isGenerator : Bool := false
  deriving Repr, BEq

/-- ECMA-262 §16 Scripts and Modules (script body lowered to one Core expression). -/
structure Program where
  body : Expr
  functions : Array FuncDef
  deriving Repr, BEq

end VerifiedJS.Core
