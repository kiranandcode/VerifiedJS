/-
  VerifiedJS — JavaScript Parser
  Recursive descent parser for ECMAScript 2020.
  Outside the verified TCB — validated by Test262 + differential testing.
-/

import VerifiedJS.Source.Lexer
import VerifiedJS.Source.AST

namespace VerifiedJS.Source

/-- Parser state. -/
structure ParserState where
  tokens : Array Token
  pos : Nat
  deriving Repr

private def parseKeywordLiteral (s : String) : Option Expr :=
  match s with
  | "true" => some (.lit (.bool true))
  | "false" => some (.lit (.bool false))
  | "null" => some (.lit .null)
  | "undefined" => some (.lit .undefined)
  | _ => none

/-- Parser monad for stateful recursive descent. -/
abbrev ParserM (α : Type) := StateT ParserState (Except String) α

private def eofTok : Token :=
  { kind := .eof, pos := { line := 0, col := 0, offset := 0 } }

private def peek : ParserM Token := do
  let st ← get
  pure <| st.tokens.getD st.pos eofTok

private def bump : ParserM Token := do
  let st ← get
  let tok := st.tokens.getD st.pos eofTok
  set { st with pos := st.pos + 1 }
  pure tok

private def isSeparator : Token → Bool
  | { kind := .newline, .. } => true
  | { kind := .punct ";", .. } => true
  | _ => false

private partial def skipSeparators : ParserM Unit := do
  let t ← peek
  if isSeparator t then
    let _ ← bump
    skipSeparators
  else
    pure ()

private def tokenDesc (t : Token) : String :=
  match t.kind with
  | .number _ => "number"
  | .string _ => "string"
  | .template _ => "template"
  | .regex _ _ => "regex"
  | .ident s => s!"identifier `{s}`"
  | .kw s => s!"keyword `{s}`"
  | .punct s => s!"`{s}`"
  | .eof => "end of input"
  | .newline => "newline"

private def failExpected {α : Type} (what : String) : ParserM α := do
  let t ← peek
  throw s!"Expected {what}, found {tokenDesc t} at {t.pos.line}:{t.pos.col}"

private def consumePunct? (p : String) : ParserM Bool := do
  let t ← peek
  match t.kind with
  | .punct p' =>
    if p = p' then
      let _ ← bump
      pure true
    else
      pure false
  | _ => pure false

private def consumeKeyword? (k : String) : ParserM Bool := do
  let t ← peek
  match t.kind with
  | .kw k' =>
    if k = k' then
      let _ ← bump
      pure true
    else
      pure false
  | _ => pure false

private def expectPunct (p : String) : ParserM Unit := do
  let ok ← consumePunct? p
  if ok then
    pure ()
  else
    failExpected s!"`{p}`"

private def expectIdent : ParserM String := do
  let t ← peek
  match t.kind with
  | .ident name =>
    let _ ← bump
    pure name
  | _ => failExpected "identifier"

private def asAssignTarget (e : Expr) : Option AssignTarget :=
  match e with
  | .ident n => some (.ident n)
  | .member obj prop => some (.member obj prop)
  | .index obj prop => some (.index obj prop)
  | _ => none

private def parsePatternFromIdent (name : String) : Pattern :=
  .ident name none

mutual

private partial def parseExprListUntil (close : String) : ParserM (List Expr) := do
  let closeNow ← consumePunct? close
  if closeNow then
    pure []
  else
    let first ← parseAssignmentM
    let rec go (acc : List Expr) : ParserM (List Expr) := do
      let comma ← consumePunct? ","
      if comma then
        let e ← parseAssignmentM
        go (e :: acc)
      else
        expectPunct close
        pure acc.reverse
    go [first]

private partial def parsePrimaryM : ParserM Expr := do
  let t ← peek
  match t.kind with
  | .number n =>
    let _ ← bump
    pure (.lit (.number n))
  | .string s =>
    let _ ← bump
    pure (.lit (.string s))
  | .regex p f =>
    let _ ← bump
    pure (.lit (.regex p f))
  | .ident n =>
    let _ ← bump
    pure (.ident n)
  | .kw "this" =>
    let _ ← bump
    pure .this
  | .kw k =>
    let _ ← bump
    match parseKeywordLiteral k with
    | some e => pure e
    | none => throw s!"Unsupported keyword expression `{k}` at {t.pos.line}:{t.pos.col}"
  | .punct "(" =>
    let _ ← bump
    let e ← parseExprM
    expectPunct ")"
    pure e
  | _ => failExpected "expression"

private partial def parsePostfixM : ParserM Expr := do
  let base ← parsePrimaryM
  let rec loop (e : Expr) : ParserM Expr := do
    if (← consumePunct? ".") then
      let prop ← expectIdent
      loop (.member e prop)
    else if (← consumePunct? "[") then
      let idx ← parseExprM
      expectPunct "]"
      loop (.index e idx)
    else if (← consumePunct? "(") then
      let args ← parseExprListUntil ")"
      loop (.call e args)
    else
      pure e
  loop base

private partial def parseUnaryM : ParserM Expr := do
  if (← consumePunct? "+") then
    return .unary .pos (← parseUnaryM)
  if (← consumePunct? "-") then
    return .unary .neg (← parseUnaryM)
  if (← consumePunct? "!") then
    return .unary .logNot (← parseUnaryM)
  if (← consumePunct? "~") then
    return .unary .bitNot (← parseUnaryM)
  if (← consumeKeyword? "typeof") then
    return .unary .typeof (← parseUnaryM)
  if (← consumeKeyword? "void") then
    return .unary .void (← parseUnaryM)
  if (← consumeKeyword? "delete") then
    return .unary .delete (← parseUnaryM)
  parsePostfixM

private partial def parseMultiplicativeM : ParserM Expr := do
  let lhs ← parseUnaryM
  let rec loop (acc : Expr) : ParserM Expr := do
    if (← consumePunct? "*") then
      let rhs ← parseUnaryM
      loop (.binary .mul acc rhs)
    else if (← consumePunct? "/") then
      let rhs ← parseUnaryM
      loop (.binary .div acc rhs)
    else if (← consumePunct? "%") then
      let rhs ← parseUnaryM
      loop (.binary .mod acc rhs)
    else
      pure acc
  loop lhs

private partial def parseAdditiveM : ParserM Expr := do
  let lhs ← parseMultiplicativeM
  let rec loop (acc : Expr) : ParserM Expr := do
    if (← consumePunct? "+") then
      let rhs ← parseMultiplicativeM
      loop (.binary .add acc rhs)
    else if (← consumePunct? "-") then
      let rhs ← parseMultiplicativeM
      loop (.binary .sub acc rhs)
    else
      pure acc
  loop lhs

private partial def parseRelationalM : ParserM Expr := do
  let lhs ← parseAdditiveM
  let rec loop (acc : Expr) : ParserM Expr := do
    if (← consumePunct? "<=") then
      let rhs ← parseAdditiveM
      loop (.binary .le acc rhs)
    else if (← consumePunct? ">=") then
      let rhs ← parseAdditiveM
      loop (.binary .ge acc rhs)
    else if (← consumePunct? "<") then
      let rhs ← parseAdditiveM
      loop (.binary .lt acc rhs)
    else if (← consumePunct? ">") then
      let rhs ← parseAdditiveM
      loop (.binary .gt acc rhs)
    else if (← consumeKeyword? "in") then
      let rhs ← parseAdditiveM
      loop (.binary .in acc rhs)
    else if (← consumeKeyword? "instanceof") then
      let rhs ← parseAdditiveM
      loop (.binary .instanceof acc rhs)
    else
      pure acc
  loop lhs

private partial def parseEqualityM : ParserM Expr := do
  let lhs ← parseRelationalM
  let rec loop (acc : Expr) : ParserM Expr := do
    if (← consumePunct? "===") then
      let rhs ← parseRelationalM
      loop (.binary .strictEq acc rhs)
    else if (← consumePunct? "!==") then
      let rhs ← parseRelationalM
      loop (.binary .strictNeq acc rhs)
    else if (← consumePunct? "==") then
      let rhs ← parseRelationalM
      loop (.binary .eq acc rhs)
    else if (← consumePunct? "!=") then
      let rhs ← parseRelationalM
      loop (.binary .neq acc rhs)
    else
      pure acc
  loop lhs

private partial def parseNullishM : ParserM Expr := do
  let lhs ← parseEqualityM
  let rec loop (acc : Expr) : ParserM Expr := do
    if (← consumePunct? "??") then
      let rhs ← parseEqualityM
      loop (.binary .nullishCoalesce acc rhs)
    else
      pure acc
  loop lhs

private partial def parseLogicalAndM : ParserM Expr := do
  let lhs ← parseNullishM
  let rec loop (acc : Expr) : ParserM Expr := do
    if (← consumePunct? "&&") then
      let rhs ← parseNullishM
      loop (.binary .logAnd acc rhs)
    else
      pure acc
  loop lhs

private partial def parseLogicalOrM : ParserM Expr := do
  let lhs ← parseLogicalAndM
  let rec loop (acc : Expr) : ParserM Expr := do
    if (← consumePunct? "||") then
      let rhs ← parseLogicalAndM
      loop (.binary .logOr acc rhs)
    else
      pure acc
  loop lhs

private partial def parseConditionalM : ParserM Expr := do
  let cond ← parseLogicalOrM
  if (← consumePunct? "?") then
    let thenE ← parseAssignmentM
    expectPunct ":"
    let elseE ← parseAssignmentM
    pure (.conditional cond thenE elseE)
  else
    pure cond

private partial def parseAssignOp? : ParserM (Option AssignOp) := do
  let t ← peek
  match t.kind with
  | .punct "=" => let _ ← bump; pure (some .assign)
  | .punct "+=" => let _ ← bump; pure (some .addAssign)
  | .punct "-=" => let _ ← bump; pure (some .subAssign)
  | .punct "*=" => let _ ← bump; pure (some .mulAssign)
  | .punct "/=" => let _ ← bump; pure (some .divAssign)
  | .punct "%=" => let _ ← bump; pure (some .modAssign)
  | .punct "**=" => let _ ← bump; pure (some .expAssign)
  | .punct "<<=" => let _ ← bump; pure (some .shlAssign)
  | .punct ">>=" => let _ ← bump; pure (some .shrAssign)
  | .punct ">>>=" => let _ ← bump; pure (some .ushrAssign)
  | .punct "&=" => let _ ← bump; pure (some .bitAndAssign)
  | .punct "|=" => let _ ← bump; pure (some .bitOrAssign)
  | .punct "^=" => let _ ← bump; pure (some .bitXorAssign)
  | .punct "&&=" => let _ ← bump; pure (some .logAndAssign)
  | .punct "||=" => let _ ← bump; pure (some .logOrAssign)
  | .punct "??=" => let _ ← bump; pure (some .nullishAssign)
  | _ => pure none

private partial def parseAssignmentM : ParserM Expr := do
  let lhs ← parseConditionalM
  match (← parseAssignOp?) with
  | none => pure lhs
  | some op =>
    match asAssignTarget lhs with
    | none =>
      throw "Invalid assignment target"
    | some target =>
      let rhs ← parseAssignmentM
      pure (.assign op target rhs)

private partial def parseExprM : ParserM Expr := do
  let first ← parseAssignmentM
  let rec loop (acc : List Expr) : ParserM Expr := do
    if (← consumePunct? ",") then
      let e ← parseAssignmentM
      loop (e :: acc)
    else
      match acc.reverse with
      | [single] => pure single
      | many => pure (.sequence many)
  loop [first]

end

private partial def parseVarDecl : ParserM VarDeclarator := do
  let name ← expectIdent
  let init ←
    if (← consumePunct? "=") then
      some <$> parseAssignmentM
    else
      pure none
  pure (.mk (parsePatternFromIdent name) init)

private partial def parseVarDecls : ParserM (List VarDeclarator) := do
  let first ← parseVarDecl
  let rec loop (acc : List VarDeclarator) : ParserM (List VarDeclarator) := do
    if (← consumePunct? ",") then
      let d ← parseVarDecl
      loop (d :: acc)
    else
      pure acc.reverse
  loop [first]

private partial def parseStmt : ParserM Stmt := do
  skipSeparators
  let t ← peek
  match t.kind with
  | .eof => failExpected "statement"
  | .punct "{" =>
    let _ ← bump
    let rec gather (acc : List Stmt) : ParserM (List Stmt) := do
      skipSeparators
      if (← consumePunct? "}") then
        pure acc.reverse
      else
        let s ← parseStmt
        gather (s :: acc)
    pure (.block (← gather []))
  | .punct ";" =>
    let _ ← bump
    pure .empty
  | .kw "return" =>
    let _ ← bump
    let next ← peek
    match next.kind with
    | .newline | .punct ";" | .punct "}" | .eof =>
      pure (.return none)
    | _ =>
      let e ← parseExprM
      pure (.return (some e))
  | .kw "var" =>
    let _ ← bump
    pure (.varDecl .var (← parseVarDecls))
  | .kw "let" =>
    let _ ← bump
    pure (.varDecl .let_ (← parseVarDecls))
  | .kw "const" =>
    let _ ← bump
    pure (.varDecl .const_ (← parseVarDecls))
  | _ =>
    let e ← parseExprM
    pure (.expr e)

private partial def parseProgram : ParserM Program := do
  let rec gather (acc : List Stmt) : ParserM (List Stmt) := do
    skipSeparators
    let t ← peek
    match t.kind with
    | .eof => pure acc.reverse
    | _ =>
      let s ← parseStmt
      gather (s :: acc)
  pure (.script (← gather []))

/-- Parse a JavaScript source string into a Program AST.
    Current implementation supports multi-token expressions and simple statements. -/
def parse (source : String) : Except String Program := do
  let toks ← tokenize source
  let init : ParserState := { tokens := toks.toArray, pos := 0 }
  (parseProgram.run init).map Prod.fst

/-- Parse a single expression (useful for testing).
    Parses and validates that only one expression was provided. -/
def parseExpr (source : String) : Except String Expr := do
  let toks ← tokenize source
  let init : ParserState := { tokens := toks.toArray, pos := 0 }
  let (e, st) ← (parseExprM.run init)
  let ((), st2) ← (skipSeparators.run st)
  let trailing := st2.tokens.getD st2.pos eofTok
  match trailing.kind with
  | .eof => pure e
  | _ => throw s!"Unexpected trailing token {tokenDesc trailing} at {trailing.pos.line}:{trailing.pos.col}"

end VerifiedJS.Source
