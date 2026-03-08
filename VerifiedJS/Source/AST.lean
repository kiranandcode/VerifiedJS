/-
  VerifiedJS — Full ECMAScript 2020 Abstract Syntax Tree
  SPEC: §11–15 (ECMAScript Language: Lexical Grammar, Expressions, Statements, Functions, Scripts and Modules)
-/

namespace VerifiedJS.Source

/-- ECMA-262 §12.1 Identifier Names and Identifiers -/
abbrev Ident := String

/-- ECMA-262 §12.8 Unary Operators and Update Expressions -/
inductive UnaryOp where
  | typeof | void | delete
  | neg | pos | bitNot | logNot
  | preInc | preDec | postInc | postDec
  deriving Repr, BEq, Hashable

/-- ECMA-262 §12.5–§12.13 Binary/Logical Operators and Relational Operators -/
inductive BinOp where
  | add | sub | mul | div | mod | exp
  | eq | neq | strictEq | strictNeq
  | lt | gt | le | ge
  | bitAnd | bitOr | bitXor | shl | shr | ushr
  | logAnd | logOr | nullishCoalesce
  | instanceof | «in»
  deriving Repr, BEq, Hashable

/-- ECMA-262 §13.15 Assignment Operators -/
inductive AssignOp where
  | assign | addAssign | subAssign | mulAssign | divAssign | modAssign
  | expAssign | shlAssign | shrAssign | ushrAssign
  | bitAndAssign | bitOrAssign | bitXorAssign
  | logAndAssign | logOrAssign | nullishAssign
  deriving Repr, BEq, Hashable

/-- ECMA-262 §14.3 Method Definitions -/
inductive MethodKind where
  | method | get | set | constructor
  deriving Repr, BEq

/-- ECMA-262 §13.3 Variable Statement and Lexical Declarations -/
inductive VarKind where
  | var | let_ | const_
  deriving Repr, BEq

/-- ECMA-262 §12.8 Literals (including ES2020 BigInt and RegExp literals) -/
inductive Literal where
  | null
  | bool (b : Bool)
  | number (n : Float)
  | bigint (digits : String)
  | string (s : String)
  | regex (pattern flags : String)
  | undefined
  deriving Repr, BEq

/-- ECMA-262 §13.7 Iteration Statements (`for ... of` modifiers). -/
inductive ForOfKind where
  | sync
  | async
  deriving Repr, BEq

/-- ECMA-262 §15.2 Import Attributes (host-defined keys/values). -/
structure ImportAttribute where
  key : String
  value : String
  deriving Repr, BEq

-- All mutually recursive AST types.
-- Lean 4 requires mutual blocks for cross-referencing inductive types.
mutual

/-- ECMA-262 §12 Expressions, §14 Function and Class Definitions, §13.3.8 Binding Patterns -/
inductive Expr where
  | lit (v : Literal)
  | ident (name : Ident)
  | this
  | «super»
  | array (elems : List (Option Expr))
  | object (props : List Property)
  | function (name : Option Ident) (params : List Pattern) (body : List Stmt)
  | arrowFunction (params : List Pattern) (body : ArrowBody)
  | «class» (name : Option Ident) (superClass : Option Expr) (body : List ClassMember)
  | unary (op : UnaryOp) (arg : Expr)
  | binary (op : BinOp) (lhs rhs : Expr)
  | assign (op : AssignOp) (lhs : AssignTarget) (rhs : Expr)
  | conditional (cond thenE elseE : Expr)
  | call (callee : Expr) (args : List Expr)
  | «new» (callee : Expr) (args : List Expr)
  | member (obj : Expr) (prop : Ident)
  | index (obj : Expr) (prop : Expr)
  | privateMember (obj : Expr) (privateName : Ident)
  | optionalChain (expr : Expr) (chain : List ChainElem)
  | template (tag : Option Expr) (parts : List TemplatePart)
  | spread (arg : Expr)
  | yield (arg : Option Expr) (delegate : Bool)
  | await (arg : Expr)
  | sequence (exprs : List Expr)
  | metaProperty (metaName propName : Ident)
  | newTarget
  | importMeta
  | importCall (source : Expr) (attrs : List ImportAttribute)
  | privateIn (privateName : Ident) (rhs : Expr)

/-- ECMA-262 §12.2.6 Object Initializer -/
inductive Property where
  | keyValue (key : PropertyKey) (value : Expr)
  | shorthand (name : Ident)
  | method (kind : MethodKind) (key : PropertyKey) (params : List Pattern) (body : List Stmt)
    (isAsync : Bool := false) (isGenerator : Bool := false)
  | spread (expr : Expr)

/-- ECMA-262 §12.2.6 Property Name (including private names in classes). -/
inductive PropertyKey where
  | ident (name : Ident)
  | string (s : String)
  | number (n : Float)
  | private_ (name : Ident)
  | computed (expr : Expr)

/-- ECMA-262 §13.3.3 Binding Patterns and §14 Formal Parameters -/
inductive Pattern where
  | ident (name : Ident) (init : Option Expr)
  | array (elems : List (Option Pattern)) (rest : Option Pattern)
  | object (props : List PatternProp) (rest : Option Pattern)
  | assign (pat : Pattern) (init : Expr)

/-- ECMA-262 §13.3.3.7 BindingProperty and shorthand binding forms -/
inductive PatternProp where
  | keyValue (key : PropertyKey) (value : Pattern)
  | shorthand (name : Ident) (init : Option Expr)

/-- ECMA-262 §13 Statements and Declarations, §14 Hoistable/Class Declarations -/
inductive Stmt where
  | expr (e : Expr)
  | block (stmts : List Stmt)
  | varDecl (kind : VarKind) (decls : List VarDeclarator)
  | «if» (cond : Expr) (then_ : Stmt) (else_ : Option Stmt)
  | while_ (cond : Expr) (body : Stmt)
  | doWhile (body : Stmt) (cond : Expr)
  | «for» (init : Option ForInit) (cond : Option Expr) (update : Option Expr) (body : Stmt)
  | forIn (kind : Option VarKind) (lhs : ForLHS) (rhs : Expr) (body : Stmt)
  | forOf (kind : Option VarKind) (lhs : ForLHS) (rhs : Expr) (body : Stmt)
  | forOfEx (kind : Option VarKind) (lhs : ForLHS) (rhs : Expr) (body : Stmt) (mode : ForOfKind)
  | «switch» (disc : Expr) (cases : List SwitchCase)
  | «try» (body : List Stmt) (catch_ : Option CatchClause) (finally_ : Option (List Stmt))
  | throw (arg : Expr)
  | «return» (arg : Option Expr)
  | «break» (label : Option Ident)
  | «continue» (label : Option Ident)
  | labeled (label : Ident) (body : Stmt)
  | with (obj : Expr) (body : Stmt)
  | debugger
  | empty
  | functionDecl (name : Ident) (params : List Pattern) (body : List Stmt)
    (isAsync : Bool) (isGenerator : Bool)
  | classDecl (name : Ident) (superClass : Option Expr) (body : List ClassMember)
  -- Legacy compatibility constructors; module-accurate forms are in ModuleDecl/ModuleItem.
  | import_ (specifiers : List ImportSpecifier) (source : String)
  | export_ (decl : ExportDecl)

/-- ECMA-262 §13.3.2 VariableDeclaration -/
inductive VarDeclarator where
  | mk (pat : Pattern) (init : Option Expr)

/-- ECMA-262 §13.7.4 ForStatement initializers -/
inductive ForInit where
  | varDecl (kind : VarKind) (decls : List VarDeclarator)
  | expr (e : Expr)

/-- ECMA-262 §13.7.5/§13.7.6 left-hand side forms in `for-in/of` heads -/
inductive ForLHS where
  | pattern (p : Pattern)
  | varDecl (kind : VarKind) (pat : Pattern)

/-- ECMA-262 §13.12 Switch Statement clauses -/
inductive SwitchCase where
  | case_ (test : Expr) (body : List Stmt)
  | default_ (body : List Stmt)

/-- ECMA-262 §13.15 Try Statement catch parameter/body -/
inductive CatchClause where
  | mk (param : Option Pattern) (body : List Stmt)

/-- ECMA-262 §14.6 Class Definitions, ClassElement and ClassStaticBlock -/
inductive ClassMember where
  | method (isStatic : Bool) (kind : MethodKind) (key : PropertyKey)
    (params : List Pattern) (body : List Stmt) (isAsync : Bool) (isGenerator : Bool)
  | property (isStatic : Bool) (key : PropertyKey) (value : Option Expr)
  | privateMethod (isStatic : Bool) (name : Ident) (params : List Pattern) (body : List Stmt)
    (isAsync : Bool) (isGenerator : Bool)
  | privateField (isStatic : Bool) (name : Ident) (value : Option Expr)
  | staticBlock (body : List Stmt)

/-- ECMA-262 §14.2 Arrow Function Definitions -/
inductive ArrowBody where
  | expr (e : Expr)
  | block (stmts : List Stmt)

/-- ECMA-262 §13.15 AssignmentTarget forms -/
inductive AssignTarget where
  | ident (name : Ident)
  | member (obj : Expr) (prop : Ident)
  | index (obj : Expr) (prop : Expr)
  | privateMember (obj : Expr) (name : Ident)
  | pattern (pat : Pattern)

/-- ECMA-262 §13.3 Optional Chaining (`?.`) chain elements -/
inductive ChainElem where
  | member (prop : Ident)
  | index (prop : Expr)
  | privateMember (name : Ident)
  | call (args : List Expr)

/-- ECMA-262 §12.2.9 Template Literals -/
inductive TemplatePart where
  | string (cooked : String) (raw : Option String := none)
  | expr (e : Expr)

/-- ECMA-262 §15.2.2 Imports: named, default, and namespace bindings -/
inductive ImportSpecifier where
  | named (imported localName : Ident)
  | default_ (localName : Ident)
  | namespace (localName : Ident)

/-- ECMA-262 §15.2.3 Exports: local to exported name mapping -/
inductive ExportSpecifier where
  | mk (localName exported : Ident)

/-- Legacy export wrapper used by current parser; see ModuleDecl for full shape. -/
inductive ExportDecl where
  | named (specifiers : List ExportSpecifier) (source : Option String)
  | default_ (expr : Expr)
  | decl (stmt : Stmt)
  | all (source : String) (alias_ : Option Ident)

/-- ECMA-262 §15.2 ImportDeclaration family with optional attributes. -/
inductive ImportDecl where
  | sideEffect (source : String) (attrs : List ImportAttribute := [])
  | withClause (specifiers : List ImportSpecifier) (source : String) (attrs : List ImportAttribute := [])

/-- ECMA-262 §15.2 ExportDeclaration family (including re-export forms). -/
inductive ExportStmt where
  | named (specifiers : List ExportSpecifier) (source : Option String)
  | defaultExpr (value : Expr)
  | defaultFunction (name : Option Ident) (params : List Pattern) (body : List Stmt)
    (isAsync : Bool := false) (isGenerator : Bool := false)
  | defaultClass (name : Option Ident) (superClass : Option Expr) (body : List ClassMember)
  | declaration (decl : Stmt)
  | allFrom (source : String) (alias_ : Option Ident)

/-- ECMA-262 §15 Script item list (`StatementListItem`) with directive prologues. -/
inductive ScriptItem where
  | directive (value : String)
  | stmt (s : Stmt)

/-- ECMA-262 §15 Module item list (`ModuleItem`). -/
inductive ModuleItem where
  | stmt (s : Stmt)
  | importDecl (d : ImportDecl)
  | exportDecl (d : ExportStmt)

end

/-- ECMA-262 §15 Scripts and Modules top-level forms.
    `script`/`module_` preserve the current parser interface.
    `scriptItems`/`moduleItems` model full ES2020 top-level grammar. -/
inductive Program where
  | script (stmts : List Stmt)
  | module_ (stmts : List Stmt)
  | scriptItems (items : List ScriptItem)
  | moduleItems (items : List ModuleItem)

end VerifiedJS.Source
