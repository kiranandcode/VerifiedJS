/-
  VerifiedJS — Elaboration: JS.AST → JS.Core
  Desugars classes, destructuring, for-in/for-of, etc. into Core primitives.
  SPEC: §14.6 (Class Definitions), §13.15.5 (Destructuring), §13.7 (Iteration)
-/

import VerifiedJS.Source.AST
import VerifiedJS.Core.Syntax

namespace VerifiedJS.Core

/-- Elaboration monad: accumulates FuncDef entries alongside Except String. -/
abbrev ElabM := StateT (Array FuncDef) (Except String)

/-- Map Source.UnaryOp to Core.UnaryOp (pre/post inc/dec and delete/typeof handled separately). -/
private def mapUnaryOp : Source.UnaryOp → Option Core.UnaryOp
  | .neg    => some .neg
  | .pos    => some .pos
  | .bitNot => some .bitNot
  | .logNot => some .logNot
  | .void   => some .void
  | _       => none

/-- Map Source.BinOp to Core.BinOp. -/
private def mapBinOp : Source.BinOp → Option Core.BinOp
  | .add           => some .add
  | .sub           => some .sub
  | .mul           => some .mul
  | .div           => some .div
  | .mod           => some .mod
  | .exp           => some .exp
  | .eq            => some .eq
  | .neq           => some .neq
  | .strictEq      => some .strictEq
  | .strictNeq     => some .strictNeq
  | .lt            => some .lt
  | .gt            => some .gt
  | .le            => some .le
  | .ge            => some .ge
  | .bitAnd        => some .bitAnd
  | .bitOr         => some .bitOr
  | .bitXor        => some .bitXor
  | .shl           => some .shl
  | .shr           => some .shr
  | .ushr          => some .ushr
  | .logAnd        => some .logAnd
  | .logOr         => some .logOr
  | .instanceof    => some .instanceof
  | .«in»          => some .«in»
  | .nullishCoalesce => none  -- no direct Core equivalent; could desugar but leave as unsupported

/-- Get the corresponding binary op for a compound assignment operator. -/
private def assignOpToBinOp : Source.AssignOp → Option Core.BinOp
  | .addAssign     => some .add
  | .subAssign     => some .sub
  | .mulAssign     => some .mul
  | .divAssign     => some .div
  | .modAssign     => some .mod
  | .expAssign     => some .exp
  | .shlAssign     => some .shl
  | .shrAssign     => some .shr
  | .ushrAssign    => some .ushr
  | .bitAndAssign  => some .bitAnd
  | .bitOrAssign   => some .bitOr
  | .bitXorAssign  => some .bitXor
  | .logAndAssign  => some .logAnd
  | .logOrAssign   => some .logOr
  | _              => none

/-- Map Source.Literal to Core.Value. -/
private def mapLiteral : Source.Literal → Core.Value
  | .null       => .null
  | .bool b     => .bool b
  | .number n   => .number n
  | .string s   => .string s
  | .undefined  => .undefined
  | .bigint _   => .undefined  -- BigInt not supported in Core
  | .regex _ _  => .undefined  -- RegExp not supported in Core

/-- The undefined literal expression. -/
private def undef : Core.Expr := .lit .undefined

/-- Extract simple parameter names from Source patterns (best effort). -/
private partial def patternToName : Source.Pattern → String
  | .ident n _     => n
  | .assign pat _  => patternToName pat
  | _              => "_"

/-- Extract parameter name list from Source patterns. -/
private def paramsToNames (ps : List Source.Pattern) : List String :=
  ps.map patternToName

/-- Sequence a list of Core expressions with `.seq`. -/
private def seqExprs : List Core.Expr → Core.Expr
  | []      => undef
  | [e]     => e
  | e :: es => .seq e (seqExprs es)

/-- Convert a property key to a string name. -/
private def propKeyToString : Source.PropertyKey → String
  | .ident name   => name
  | .string s     => s
  | .number n     => toString n
  | .private_ name => "_private_" ++ name
  | .computed _   => "__computed__"

mutual

private partial def propKeyAccessExpr (obj : Core.Expr) (k : Source.PropertyKey) : ElabM Core.Expr := do
  match k with
  | .computed ke =>
    pure (.getIndex obj (← elabExpr ke))
  | _ =>
    pure (.getProp obj (propKeyToString k))

private partial def elabPatternAssignExpr (pat : Source.Pattern) (valueExpr : Core.Expr) : ElabM Core.Expr := do
  match pat with
  | .ident name none =>
    pure (.assign name valueExpr)
  | .ident name (some initExpr) => do
    let initCore ← elabExpr initExpr
    pure (.assign name (.«if» (.binary .strictEq valueExpr (.lit .undefined)) initCore valueExpr))
  | .assign inner initExpr => do
    let initCore ← elabExpr initExpr
    let resolved := .«if» (.binary .strictEq valueExpr (.lit .undefined)) initCore valueExpr
    elabPatternAssignExpr inner resolved
  | .object props rest => do
    let mut assigns : List Core.Expr := []
    for p in props do
      let next ← match p with
        | .keyValue key subpat => do
          let propExpr ← propKeyAccessExpr valueExpr key
          elabPatternAssignExpr subpat propExpr
        | .shorthand name initOpt => do
          let base := .getProp valueExpr name
          match initOpt with
          | some initExpr => do
            let initCore ← elabExpr initExpr
            pure (.assign name (.«if» (.binary .strictEq base (.lit .undefined)) initCore base))
          | none =>
            pure (.assign name base)
      assigns := assigns ++ [next]
    let restAssign ← match rest with
      | some restPat => elabPatternAssignExpr restPat valueExpr
      | none => pure undef
    pure (seqExprs (assigns ++ [restAssign]))
  | .array elems rest => do
    let mut assigns : List Core.Expr := []
    let mut idx : Nat := 0
    for elem in elems do
      match elem with
      | some subpat => do
        let elemExpr : Core.Expr := .getIndex valueExpr (.lit (.number (Float.ofNat idx)))
        let next ← elabPatternAssignExpr subpat elemExpr
        assigns := assigns ++ [next]
      | none => pure ()
      idx := idx + 1
    let restAssign ← match rest with
      | some restPat => elabPatternAssignExpr restPat valueExpr
      | none => pure undef
    pure (seqExprs (assigns ++ [restAssign]))

/-- Elaborate a Source expression to a Core expression. -/
private partial def elabExpr (e : Source.Expr) : ElabM Core.Expr := do
  match e with
  | .lit v => pure (.lit (mapLiteral v))
  | .ident name => pure (.var name)
  | .this => pure .this
  | .«super» => pure (.var "super")

  | .array elems => do
    let mut coreElems : List Core.Expr := []
    for optE in elems do
      match optE with
      | some ex => coreElems := coreElems ++ [← elabExpr ex]
      | none    => coreElems := coreElems ++ [undef]
    pure (.arrayLit coreElems)

  | .object props => do
    let mut corePairs : List (PropName × Core.Expr) := []
    for p in props do
      match p with
      | .keyValue k v => do
        let key := propKeyToString k
        let val ← elabExpr v
        corePairs := corePairs ++ [(key, val)]
      | .shorthand name =>
        corePairs := corePairs ++ [(name, .var name)]
      | .method _kind k params body isAsync isGenerator => do
        let key := propKeyToString k
        let bodyExpr ← elabStmts body
        corePairs := corePairs ++ [(key, .functionDef none (paramsToNames params) bodyExpr isAsync isGenerator)]
      | .spread ex => do
        -- spread in object literal: approximate as a single entry
        let val ← elabExpr ex
        corePairs := corePairs ++ [("__spread__", val)]
    pure (.objectLit corePairs)

  | .function name params body => do
    let bodyExpr ← elabStmts body
    pure (.functionDef name (paramsToNames params) bodyExpr false false)

  | .arrowFunction params body => do
    let bodyExpr ← match body with
      | .expr ex    => elabExpr ex
      | .block stmts => elabStmts stmts
    pure (.functionDef none (paramsToNames params) bodyExpr false false)

  | .«class» _ _ _ => pure undef  -- classes not supported in Core

  | .unary op arg => do
    match op with
    | .typeof => do
      let a ← elabExpr arg
      pure (.typeof a)
    | .delete => do
      match arg with
      | .member obj prop => do
        let o ← elabExpr obj
        pure (.deleteProp o prop)
      | _ => do
        let _ ← elabExpr arg
        pure (.lit (.bool true))
    | .preInc => do
      -- ++x => x = x + 1
      match arg with
      | .ident name => pure (.assign name (.binary .add (.var name) (.lit (.number 1.0))))
      | _ => do
        let a ← elabExpr arg
        pure (.binary .add a (.lit (.number 1.0)))
    | .preDec => do
      match arg with
      | .ident name => pure (.assign name (.binary .sub (.var name) (.lit (.number 1.0))))
      | _ => do
        let a ← elabExpr arg
        pure (.binary .sub a (.lit (.number 1.0)))
    | .postInc => do
      -- x++ => (let _tmp = x; x = x + 1; _tmp)
      match arg with
      | .ident name =>
        pure (.«let» "__postInc_tmp" (.var name)
          (.seq (.assign name (.binary .add (.var name) (.lit (.number 1.0))))
                (.var "__postInc_tmp")))
      | _ => do
        let a ← elabExpr arg
        pure (.binary .add a (.lit (.number 1.0)))
    | .postDec => do
      match arg with
      | .ident name =>
        pure (.«let» "__postDec_tmp" (.var name)
          (.seq (.assign name (.binary .sub (.var name) (.lit (.number 1.0))))
                (.var "__postDec_tmp")))
      | _ => do
        let a ← elabExpr arg
        pure (.binary .sub a (.lit (.number 1.0)))
    | _ => do
      match mapUnaryOp op with
      | some cop => do
        let a ← elabExpr arg
        pure (.unary cop a)
      | none => do
        let _ ← elabExpr arg
        pure undef

  | .binary op lhs rhs => do
    match mapBinOp op with
    | some cop => do
      let l ← elabExpr lhs
      let r ← elabExpr rhs
      pure (.binary cop l r)
    | none => do
      -- nullishCoalesce: desugar to let _t = lhs; if (_t == null) rhs else _t
      -- (approximate: uses == null which catches null/undefined)
      let l ← elabExpr lhs
      let r ← elabExpr rhs
      pure (.«let» "__nc_tmp" l
        (.«if» (.binary .eq (.var "__nc_tmp") (.lit .null)) r (.var "__nc_tmp")))

  | .assign op target rhs => do
    let rhsExpr ← elabExpr rhs
    elabAssign op target rhsExpr

  | .conditional cond thenE elseE => do
    let c ← elabExpr cond
    let t ← elabExpr thenE
    let el ← elabExpr elseE
    pure (.«if» c t el)

  | .call callee args => do
    let c ← elabExpr callee
    let as_ ← args.mapM elabExpr
    pure (.call c as_)

  | .«new» callee args => do
    let c ← elabExpr callee
    let as_ ← args.mapM elabExpr
    pure (.newObj c as_)

  | .member obj prop => do
    let o ← elabExpr obj
    pure (.getProp o prop)

  | .index obj prop => do
    let o ← elabExpr obj
    let p ← elabExpr prop
    pure (.getIndex o p)

  | .privateMember obj name => do
    let o ← elabExpr obj
    pure (.getProp o ("_private_" ++ name))

  | .optionalChain expr_ _chain => do
    -- Approximate: just elaborate the base expression
    elabExpr expr_

  | .template _tag parts => do
    -- Desugar template to string concatenation
    let mut result : Core.Expr := .lit (.string "")
    for part in parts do
      match part with
      | .string cooked _ => do
        result := .binary .add result (.lit (.string cooked))
      | .expr ex => do
        let e ← elabExpr ex
        result := .binary .add result e
    pure result

  | .spread arg => do
    -- spread as expression: just elaborate the argument
    elabExpr arg

  | .yield arg delegate => do
    let a ← match arg with
      | some ex => do pure (some (← elabExpr ex))
      | none    => pure none
    pure (.yield a delegate)

  | .await arg => do
    let a ← elabExpr arg
    pure (.await a)

  | .sequence exprs => do
    let coreExprs ← exprs.mapM elabExpr
    pure (seqExprs coreExprs)

  | .metaProperty _ _ => pure undef
  | .newTarget => pure undef
  | .importMeta => pure undef
  | .importCall _ _ => pure undef
  | .privateIn _ _ => pure undef

/-- Elaborate an assignment expression. -/
private partial def elabAssign (op : Source.AssignOp) (target : Source.AssignTarget) (rhsExpr : Core.Expr) : ElabM Core.Expr := do
  match target with
  | .ident name =>
    match op with
    | .assign => pure (.assign name rhsExpr)
    | .nullishAssign =>
      pure (.«if» (.binary .eq (.var name) (.lit .null)) (.assign name rhsExpr) (.var name))
    | _ =>
      match assignOpToBinOp op with
      | some bop => pure (.assign name (.binary bop (.var name) rhsExpr))
      | none => pure (.assign name rhsExpr)
  | .member obj prop => do
    let o ← elabExpr obj
    match op with
    | .assign => pure (.setProp o prop rhsExpr)
    | _ =>
      match assignOpToBinOp op with
      | some bop =>
        pure (.setProp o prop (.binary bop (.getProp o prop) rhsExpr))
      | none => pure (.setProp o prop rhsExpr)
  | .index obj idx => do
    let o ← elabExpr obj
    let i ← elabExpr idx
    match op with
    | .assign => pure (.setIndex o i rhsExpr)
    | _ =>
      match assignOpToBinOp op with
      | some bop =>
        pure (.setIndex o i (.binary bop (.getIndex o i) rhsExpr))
      | none => pure (.setIndex o i rhsExpr)
  | .privateMember obj name => do
    let o ← elabExpr obj
    let pname := "_private_" ++ name
    match op with
    | .assign => pure (.setProp o pname rhsExpr)
    | _ =>
      match assignOpToBinOp op with
      | some bop =>
        pure (.setProp o pname (.binary bop (.getProp o pname) rhsExpr))
      | none => pure (.setProp o pname rhsExpr)
  | .pattern pat =>
    let tmpName := "__assign_pat_tmp"
    let assignExpr ← elabPatternAssignExpr pat (.var tmpName)
    pure (.«let» tmpName rhsExpr (.seq assignExpr (.var tmpName)))

/-- Elaborate a Source statement to a Core expression. -/
private partial def elabStmt (s : Source.Stmt) : ElabM Core.Expr := do
  match s with
  | .expr e => elabExpr e
  | .block stmts => elabStmts stmts
  | .varDecl _kind decls => elabVarDecls decls

  | .«if» cond then_ else_ => do
    let c ← elabExpr cond
    let t ← elabStmt then_
    let el ← match else_ with
      | some s => elabStmt s
      | none   => pure undef
    pure (.«if» c t el)

  | .while_ cond body => do
    let c ← elabExpr cond
    let b ← elabStmt body
    pure (.while_ c b)

  | .doWhile body cond => do
    -- do { body } while(cond)  =>  body; while(cond) body
    let b ← elabStmt body
    let c ← elabExpr cond
    pure (.seq b (.while_ c b))

  | .«for» init cond update body => do
    -- for(init; cond; update) body => init; while(cond) { body; update }
    let initExpr ← match init with
      | some (.varDecl _kind decls) => elabVarDecls decls
      | some (.expr e) => elabExpr e
      | none => pure undef
    let condExpr ← match cond with
      | some e => elabExpr e
      | none   => pure (.lit (.bool true))
    let updateExpr ← match update with
      | some e => elabExpr e
      | none   => pure undef
    let bodyExpr ← elabStmt body
    let whileBody := .seq bodyExpr updateExpr
    pure (.seq initExpr (.while_ condExpr whileBody))

  | .forIn _ _ _ _ => pure undef  -- for-in not supported
  | .forOf _ _ _ _ => pure undef  -- for-of not supported
  | .forOfEx _ _ _ _ _ => pure undef

  | .«switch» disc cases => do
    let d ← elabExpr disc
    -- Desugar to: let __sw = disc; if (__sw === case0) body0 else if ...
    let tmpName := "__switch_disc"
    let ifChain ← elabSwitchCases tmpName cases
    pure (.«let» tmpName d ifChain)

  | .«try» body catch_ finally_ => do
    let bodyExpr ← elabStmts body
    let finallyExpr ← match finally_ with
      | some stmts => do pure (some (← elabStmts stmts))
      | none       => pure none
    match catch_ with
    | some (.mk param cbody) => do
      let paramName := match param with
        | some (.ident n _) => n
        | _ => "__catch_err"
      let catchBody ← elabStmts cbody
      pure (.tryCatch bodyExpr paramName catchBody finallyExpr)
    | none =>
      match finallyExpr with
      | some fin => pure (.tryCatch bodyExpr "__unused" (.throw (.var "__unused")) (some fin))
      | none     => pure bodyExpr

  | .throw arg => do
    let a ← elabExpr arg
    pure (.throw a)

  | .«return» arg => do
    match arg with
    | some e => do
      let a ← elabExpr e
      pure (.«return» (some a))
    | none => pure (.«return» none)

  | .«break» label => pure (.«break» label)
  | .«continue» label => pure (.«continue» label)

  | .labeled label body => do
    let b ← elabStmt body
    pure (.labeled label b)

  | .with _ body => elabStmt body  -- `with` not supported; just elaborate body
  | .debugger => pure undef
  | .empty => pure undef

  | .functionDecl name params body isAsync isGenerator => do
    let bodyExpr ← elabStmts body
    let fd : FuncDef := {
      name := name
      params := paramsToNames params
      body := bodyExpr
      isAsync := isAsync
      isGenerator := isGenerator
    }
    modify fun fns => fns.push fd
    -- Bind the function name in scope
    pure (.assign name (.functionDef (some name) (paramsToNames params) bodyExpr isAsync isGenerator))

  | .classDecl _ _ _ => pure undef  -- classes not supported
  | .import_ _ _ => pure undef       -- imports not supported in Core
  | .export_ decl => elabExportDecl decl

/-- Elaborate a list of variable declarators. -/
private partial def elabVarDecls (decls : List Source.VarDeclarator) : ElabM Core.Expr := do
  let mut result : List Core.Expr := []
  for d in decls do
    match d with
    | .mk pat initOpt => do
      let name := patternToName pat
      let initExpr ← match initOpt with
        | some e => elabExpr e
        | none   => pure undef
      result := result ++ [.«let» name initExpr undef]
  -- We return a placeholder; the actual threading into body happens in elabStmtsList
  pure (seqExprs result)

/-- Elaborate a list of statements, threading var decls into subsequent code. -/
private partial def elabStmts (stmts : List Source.Stmt) : ElabM Core.Expr := do
  elabStmtsList stmts

/-- Helper to elaborate a list of statements, threading let-bindings forward. -/
private partial def elabStmtsList (stmts : List Source.Stmt) : ElabM Core.Expr := do
  match stmts with
  | [] => pure undef
  | [s] => elabStmt s
  | (.varDecl _kind decls) :: rest => do
    -- Thread variable declarations as let-bindings around the rest
    let restExpr ← elabStmtsList rest
    elabVarDeclsWithBody decls restExpr
  | s :: rest => do
    let e ← elabStmt s
    let r ← elabStmtsList rest
    pure (.seq e r)

/-- Wrap variable declarations as nested let-bindings around a body expression. -/
private partial def elabVarDeclsWithBody (decls : List Source.VarDeclarator) (body : Core.Expr) : ElabM Core.Expr := do
  match decls with
  | [] => pure body
  | (.mk pat initOpt) :: rest => do
    let name := patternToName pat
    let initExpr ← match initOpt with
      | some e => elabExpr e
      | none   => pure undef
    let inner ← elabVarDeclsWithBody rest body
    pure (.«let» name initExpr inner)

/-- Elaborate switch cases to nested if-else chain. -/
private partial def elabSwitchCases (discVar : String) (cases : List Source.SwitchCase) : ElabM Core.Expr := do
  match cases with
  | [] => pure undef
  | (.default_ body) :: _ => elabStmts body
  | (.case_ test body) :: rest => do
    let t ← elabExpr test
    let b ← elabStmts body
    let r ← elabSwitchCases discVar rest
    pure (.«if» (.binary .strictEq (.var discVar) t) b r)

/-- Elaborate a legacy export declaration. -/
private partial def elabExportDecl (d : Source.ExportDecl) : ElabM Core.Expr := do
  match d with
  | .default_ ex => elabExpr ex
  | .decl st => elabStmt st
  | _ => pure undef

end

/-- Elaborate a ScriptItem to a statement. -/
private partial def elabScriptItem (item : Source.ScriptItem) : ElabM Core.Expr := do
  match item with
  | .directive _ => pure undef
  | .stmt s => elabStmt s

/-- Elaborate a list of ScriptItems. -/
private partial def elabScriptItems (items : List Source.ScriptItem) : ElabM Core.Expr := do
  let exprs ← items.mapM elabScriptItem
  pure (seqExprs exprs)

/-- Elaborate an ExportStmt. -/
private partial def elabExportStmt (d : Source.ExportStmt) : ElabM Core.Expr := do
  match d with
  | .defaultExpr v => elabExpr v
  | .defaultFunction name params body isAsync isGenerator => do
    let bodyExpr ← elabStmts body
    let funcName := name.getD "__default_export"
    let fd : FuncDef := {
      name := funcName
      params := paramsToNames params
      body := bodyExpr
      isAsync := isAsync
      isGenerator := isGenerator
    }
    modify fun fns => fns.push fd
    pure (.functionDef name (paramsToNames params) bodyExpr isAsync isGenerator)
  | .declaration decl => elabStmt decl
  | .defaultClass _ _ _ => pure undef
  | .named _ _ => pure undef
  | .allFrom _ _ => pure undef

/-- Elaborate a ModuleItem to a Core expression. -/
private partial def elabModuleItem (item : Source.ModuleItem) : ElabM Core.Expr := do
  match item with
  | .stmt s => elabStmt s
  | .importDecl _ => pure undef
  | .exportDecl d => elabExportStmt d

/-- Elaborate a list of ModuleItems. -/
private partial def elabModuleItems (items : List Source.ModuleItem) : ElabM Core.Expr := do
  let exprs ← items.mapM elabModuleItem
  pure (seqExprs exprs)

/-- Elaborate a full JS AST program into Core IL. -/
def elaborate (prog : Source.Program) : Except String Program := do
  let (bodyExpr, funcs) ← run prog #[]
  pure { body := bodyExpr, functions := funcs }
where
  run (prog : Source.Program) (initFuncs : Array FuncDef) : Except String (Core.Expr × Array FuncDef) := do
    match prog with
    | .script stmts => (elabStmts stmts).run initFuncs
    | .module_ stmts => (elabStmts stmts).run initFuncs
    | .scriptItems items => (elabScriptItems items).run initFuncs
    | .moduleItems items => (elabModuleItems items).run initFuncs

end VerifiedJS.Core
