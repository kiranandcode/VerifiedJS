/-
  VerifiedJS - JavaScript Parser
  Recursive descent parser for ECMAScript 2020.
  Outside the verified TCB - validated by Test262 + differential testing.

  Grammar coverage targets ECMA-262 (2020):
  - Sec 12 Expressions
  - Sec 13 Statements and Declarations
  - Sec 14 Functions and Classes
  - Sec 15 Scripts and Modules
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
abbrev ParserM (a : Type) := StateT ParserState (Except String) a

private def eofTok : Token :=
  { kind := .eof, pos := { line := 0, col := 0, offset := 0 } }

private def peek : ParserM Token := do
  let st <- get
  pure <| st.tokens.getD st.pos eofTok

private def peekN (n : Nat) : ParserM Token := do
  let st <- get
  pure <| st.tokens.getD (st.pos + n) eofTok

private def bump : ParserM Token := do
  let st <- get
  let tok := st.tokens.getD st.pos eofTok
  set { st with pos := st.pos + 1 }
  pure tok

private def isSeparator : Token -> Bool
  | { kind := .newline, .. } => true
  | { kind := .punct ";", .. } => true
  | _ => false

private partial def skipSeparators : ParserM Unit := do
  let t <- peek
  if isSeparator t then
    let _ <- bump
    skipSeparators
  else
    pure ()

private partial def skipNewlines : ParserM Unit := do
  let t <- peek
  match t.kind with
  | .newline =>
    let _ <- bump
    skipNewlines
  | _ => pure ()

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

private def failExpected {a : Type} (what : String) : ParserM a := do
  let t <- peek
  throw s!"Expected {what}, found {tokenDesc t} at {t.pos.line}:{t.pos.col}"

private def consumePunct? (p : String) : ParserM Bool := do
  let t <- peek
  match t.kind with
  | .punct p' =>
    if p = p' then
      let _ <- bump
      pure true
    else
      pure false
  | _ => pure false

private def consumeKeyword? (k : String) : ParserM Bool := do
  let t <- peek
  match t.kind with
  | .kw k' =>
    if k = k' then
      let _ <- bump
      pure true
    else
      pure false
  | _ => pure false

private def consumeWord? (w : String) : ParserM Bool := do
  let t <- peek
  match t.kind with
  | .kw w' | .ident w' =>
    if w = w' then
      let _ <- bump
      pure true
    else
      pure false
  | _ => pure false

private def expectPunct (p : String) : ParserM Unit := do
  let ok <- consumePunct? p
  if ok then
    pure ()
  else
    failExpected s!"`{p}`"

private def expectKeyword (k : String) : ParserM Unit := do
  let ok <- consumeKeyword? k
  if ok then
    pure ()
  else
    failExpected s!"keyword `{k}`"

private def expectWord (w : String) : ParserM Unit := do
  let ok <- consumeWord? w
  if ok then
    pure ()
  else
    failExpected s!"keyword/identifier `{w}`"

private def expectIdent : ParserM String := do
  let t <- peek
  match t.kind with
  | .ident name =>
    let _ <- bump
    pure name
  | _ => failExpected "identifier"

private def parseIdentLike : ParserM String := do
  let t <- peek
  match t.kind with
  | .ident name =>
    let _ <- bump
    pure name
  | .kw name =>
    let _ <- bump
    pure name
  | _ => failExpected "identifier"

/-- ECMA-262 §15.2.2 Parse imported bindings and source string. -/
private partial def parseImportDeclStmt : ParserM Stmt := do
  let parseSourceString : ParserM String := do
    let tk <- peek
    match tk.kind with
    | .string s => let _ <- bump; pure s
    | _ => throw "Expected import source string literal"

  let parseNamedSpecifiers : ParserM (List ImportSpecifier) := do
    expectPunct "{"
    skipNewlines
    if (← consumePunct? "}") then
      pure []
    else
      let rec loop (acc : List ImportSpecifier) : ParserM (List ImportSpecifier) := do
        skipNewlines
        let imported <- parseIdentLike
        let localName <-
          if (← consumeWord? "as") then
            parseIdentLike
          else
            pure imported
        let spec := ImportSpecifier.named imported localName
        if (← consumePunct? ",") then
          skipNewlines
          if (← consumePunct? "}") then
            pure (List.reverse (spec :: acc))
          else
            loop (spec :: acc)
        else
          expectPunct "}"
          pure (List.reverse (spec :: acc))
      loop []

  let parseNamespaceSpecifier : ParserM ImportSpecifier := do
    expectPunct "*"
    expectWord "as"
    ImportSpecifier.namespace <$> parseIdentLike

  let next <- peek
  match next.kind with
  | .string source =>
    let _ <- bump
    pure (.import_ [] source)
  | .punct "*" =>
    let ns <- parseNamespaceSpecifier
    expectWord "from"
    pure (.import_ [ns] (← parseSourceString))
  | .punct "{" =>
    let named <- parseNamedSpecifiers
    expectWord "from"
    pure (.import_ named (← parseSourceString))
  | .ident _ | .kw _ =>
    let defaultBinding <- parseIdentLike
    let defaultSpec := ImportSpecifier.default_ defaultBinding
    if (← consumePunct? ",") then
      let nextAfterComma <- peek
      let combined <- match nextAfterComma.kind with
        | .punct "*" =>
          let ns <- parseNamespaceSpecifier
          pure [defaultSpec, ns]
        | .punct "{" =>
          let named <- parseNamedSpecifiers
          pure (defaultSpec :: named)
        | _ => throw "Expected `*` or `{` after default import binding"
      expectWord "from"
      pure (.import_ combined (← parseSourceString))
    else
      expectWord "from"
      pure (.import_ [defaultSpec] (← parseSourceString))
  | _ =>
    throw "Invalid import declaration"

private def asAssignTarget (e : Expr) : Option AssignTarget :=
  match e with
  | .ident n => some (.ident n)
  | .member obj prop => some (.member obj prop)
  | .index obj prop => some (.index obj prop)
  | _ => none

private def parsePatternFromIdent (name : String) : Pattern :=
  .ident name none

private partial def skipBalancedPunct (openP closeP : String) (depth : Nat := 1) : ParserM Unit := do
  if depth = 0 then
    pure ()
  else
    let t <- bump
    match t.kind with
    | .eof => throw s!"Unterminated balanced token `{openP}`"
    | .punct p =>
      if p = openP then
        skipBalancedPunct openP closeP (depth + 1)
      else if p = closeP then
        skipBalancedPunct openP closeP (depth - 1)
      else
        skipBalancedPunct openP closeP depth
    | _ => skipBalancedPunct openP closeP depth

private partial def parseBindingPatternM : ParserM Pattern := do
  skipNewlines
  let _ <- consumePunct? "..."
  let t <- peek
  match t.kind with
  | .ident name =>
    let _ <- bump
    pure (.ident name none)
  | .kw name =>
    let _ <- bump
    pure (.ident name none)
  | .punct "{" =>
    let _ <- bump
    skipBalancedPunct "{" "}"
    pure (.ident "__objPattern" none)
  | .punct "[" =>
    let _ <- bump
    skipBalancedPunct "[" "]"
    pure (.ident "__arrPattern" none)
  | _ => failExpected "binding pattern"

private def parsePatternFromExpr (e : Expr) : Option Pattern :=
  match e with
  | .ident n => some (.ident n none)
  | _ => none

private def tokenIsPunct (t : Token) (p : String) : Bool :=
  match t.kind with
  | .punct p' => p' = p
  | _ => false

private def tokenIsKeyword (t : Token) (k : String) : Bool :=
  match t.kind with
  | .kw k' => k' = k
  | _ => false

private def parseSemiOpt : ParserM Unit := do
  let _ <- consumePunct? ";"
  pure ()

private def liftExcept {a : Type} (r : Except String a) : ParserM a :=
  match r with
  | .ok v => pure v
  | .error e => throw e

private partial def skipBalancedBlock : Nat → ParserM Unit := fun depth => do
  if depth = 0 then
    pure ()
  else
    let t <- bump
    match t.kind with
    | .eof => throw "Unterminated block"
    | .punct "{" => skipBalancedBlock (depth + 1)
    | .punct "}" => skipBalancedBlock (depth - 1)
    | _ => skipBalancedBlock depth

mutual

private partial def parseExprListUntil (close : String) : ParserM (List Expr) := do
  skipNewlines
  let closeNow <- consumePunct? close
  if closeNow then
    pure []
  else
    let first <-
      if (← consumePunct? "...") then
        pure (.spread (← parseAssignmentM))
      else
        parseAssignmentM
    let rec go (acc : List Expr) : ParserM (List Expr) := do
      skipNewlines
      let comma <- consumePunct? ","
      if comma then
        skipNewlines
        if (← consumePunct? close) then
          pure acc.reverse
        else
          let e <-
            if (← consumePunct? "...") then
              pure (.spread (← parseAssignmentM))
            else
              parseAssignmentM
          go (e :: acc)
      else
        expectPunct close
        pure acc.reverse
    go [first]

private partial def parseParamPatternM : ParserM Pattern := do
  let base <- parseBindingPatternM
  if (← consumePunct? "=") then
    pure (.assign base (← parseAssignmentM))
  else
    pure base

private partial def parseParamListAfterOpen : ParserM (List Pattern) := do
  skipNewlines
  if (← consumePunct? ")") then
    pure []
  else
    let first <- parseParamPatternM
    let rec go (acc : List Pattern) : ParserM (List Pattern) := do
      skipNewlines
      if (← consumePunct? ",") then
        skipNewlines
        if (← consumePunct? ")") then
          pure acc.reverse
        else
          let p <- parseParamPatternM
          go (p :: acc)
      else
        expectPunct ")"
        pure acc.reverse
    go [first]

private partial def parseParamList : ParserM (List Pattern) := do
  expectPunct "("
  parseParamListAfterOpen

private partial def parseFunctionBody : ParserM (List Stmt) := do
  expectPunct "{"
  skipBalancedBlock 1
  pure []

private partial def parsePropertyKey : ParserM PropertyKey := do
  if (← consumePunct? "#") then
    return .private_ (← parseIdentLike)
  let t <- peek
  match t.kind with
  | .ident n =>
    let _ <- bump
    pure (.ident n)
  | .kw n =>
    let _ <- bump
    pure (.ident n)
  | .string s =>
    let _ <- bump
    pure (.string s)
  | .number n =>
    let _ <- bump
    pure (.number n)
  | .punct "[" =>
    let _ <- bump
    let e <- parseExprM
    expectPunct "]"
    pure (.computed e)
  | _ => failExpected "property key"

private partial def parseObjectLiteral : ParserM Expr := do
  expectPunct "{"
  let rec loop (acc : List Property) : ParserM Expr := do
    skipSeparators
    if (← consumePunct? "}") then
      pure (.object acc.reverse)
    else if (← consumePunct? "...") then
      let spreadExpr <- parseAssignmentM
      let _ <- consumePunct? ","
      loop (.spread spreadExpr :: acc)
    else
      let key <- parsePropertyKey
      if (← consumePunct? ":") then
        let value <- parseAssignmentM
        let _ <- consumePunct? ","
        loop (.keyValue key value :: acc)
      else
        let t <- peek
        if tokenIsPunct t "(" then
          let params <- parseParamList
          let body <- parseFunctionBody
          let _ <- consumePunct? ","
          loop (.method .method key params body :: acc)
        else
          match key with
          | .ident name =>
            let _ <- consumePunct? ","
            loop (.shorthand name :: acc)
          | _ =>
            throw "Object literal property must be key:value or method"
  loop []

private partial def parseArrayLiteral : ParserM Expr := do
  expectPunct "["
  let rec loop (acc : List (Option Expr)) : ParserM Expr := do
    skipSeparators
    if (← consumePunct? "]") then
      pure (.array acc.reverse)
    else if (← consumePunct? ",") then
      loop (none :: acc)
    else
      let e <-
        if (← consumePunct? "...") then
          return .spread (← parseAssignmentM)
        else
          parseAssignmentM
      if (← consumePunct? ",") then
        loop (some e :: acc)
      else
        expectPunct "]"
        pure (.array (List.reverse (some e :: acc)))
  loop []

private partial def parseClassElement : ParserM ClassMember := do
  let isStatic <- consumeKeyword? "static"
  let kind : MethodKind <-
    if (← consumeKeyword? "get") then pure .get
    else if (← consumeKeyword? "set") then pure .set
    else pure .method
  let isGenerator <- consumePunct? "*"
  let isAsync <- consumeKeyword? "async"
  let key <- parsePropertyKey
  if (← consumePunct? "(") then
    let st <- get
    set { st with pos := st.pos - 1 }
    let params <- parseParamList
    let body <- parseFunctionBody
    pure (.method isStatic kind key params body isAsync isGenerator)
  else
    let value <-
      if (← consumePunct? "=") then
        some <$> parseAssignmentM
      else
        pure none
    parseSemiOpt
    pure (.property isStatic key value)

private partial def parseClassBody : ParserM (List ClassMember) := do
  expectPunct "{"
  let rec loop (acc : List ClassMember) : ParserM (List ClassMember) := do
    skipSeparators
    if (← consumePunct? "}") then
      pure acc.reverse
    else
      let m <- parseClassElement
      loop (m :: acc)
  loop []

private partial def parseFunctionExpr : ParserM Expr := do
  expectKeyword "function"
  let isGen <- consumePunct? "*"
  let _ := isGen
  let name <- (do
    let t <- peek
    match t.kind with
    | .ident n =>
      let _ <- bump
      pure (some n)
    | _ => pure none)
  let params <- parseParamList
  let body <- parseFunctionBody
  pure (.function name params body)

private partial def parseClassExpr : ParserM Expr := do
  expectKeyword "class"
  let name <- (do
    let t <- peek
    match t.kind with
    | .ident n => let _ <- bump; pure (some n)
    | _ => pure none)
  let superClass <- if (← consumeKeyword? "extends") then some <$> parseAssignmentM else pure none
  let body <- parseClassBody
  pure (.class name superClass body)

private partial def parsePrimaryM : ParserM Expr := do
  skipNewlines
  let t <- peek
  match t.kind with
  | .number n =>
    let _ <- bump
    pure (.lit (.number n))
  | .string s =>
    let _ <- bump
    pure (.lit (.string s))
  | .regex p f =>
    let _ <- bump
    pure (.lit (.regex p f))
  | .ident n =>
    let _ <- bump
    pure (.ident n)
  | .kw "this" =>
    let _ <- bump
    pure .this
  | .kw "function" =>
    parseFunctionExpr
  | .kw "class" =>
    parseClassExpr
  | .kw k =>
    let _ <- bump
    match parseKeywordLiteral k with
    | some e => pure e
    | none =>
      if k = "import" then
        pure (.ident "import")
      else
        throw s!"Unsupported keyword expression `{k}` at {t.pos.line}:{t.pos.col}"
  | .template parts =>
    let _ <- bump
    pure (.template none (parts.map (fun s => .string s)))
  | .punct "(" =>
    let _ <- bump
    let e <- parseExprM
    expectPunct ")"
    pure e
  | .punct "[" =>
    parseArrayLiteral
  | .punct "{" =>
    parseObjectLiteral
  | _ => failExpected "expression"

private partial def parsePostfixM : ParserM Expr := do
  let base <- parsePrimaryM
  let rec loop (e : Expr) : ParserM Expr := do
    skipNewlines
    if (← consumePunct? ".") then
      if (← consumePunct? "#") then
        let name <- parseIdentLike
        loop (.privateMember e name)
      else
        let prop <- parseIdentLike
        loop (.member e prop)
    else if (← consumePunct? "?.") then
      let t <- peek
      match t.kind with
      | .ident prop =>
        let _ <- bump
        loop (.optionalChain e [.member prop])
      | .punct "[" =>
        let _ <- bump
        let idx <- parseExprM
        expectPunct "]"
        loop (.optionalChain e [.index idx])
      | .punct "(" =>
        let _ <- bump
        let args <- parseExprListUntil ")"
        loop (.optionalChain e [.call args])
      | _ => failExpected "optional chaining target"
    else if (← consumePunct? "[") then
      let idx <- parseExprM
      expectPunct "]"
      loop (.index e idx)
    else if (← consumePunct? "(") then
      let args <- parseExprListUntil ")"
      loop (.call e args)
    else
      let t <- peek
      match t.kind with
      | .template parts =>
        let _ <- bump
        loop (.template (some e) (parts.map (fun s => .string s)))
      | _ =>
        pure e
  let withPost <- loop base
  if (← consumePunct? "++") then
    pure (.unary .postInc withPost)
  else if (← consumePunct? "--") then
    pure (.unary .postDec withPost)
  else
    pure withPost

private partial def parseUnaryM : ParserM Expr := do
  if (← consumePunct? "++") then
    return .unary .preInc (← parseUnaryM)
  if (← consumePunct? "--") then
    return .unary .preDec (← parseUnaryM)
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
  if (← consumeKeyword? "await") then
    return .await (← parseUnaryM)
  if (← consumeKeyword? "yield") then
    let delegated <- consumePunct? "*"
    let t <- peek
    match t.kind with
    | .newline | .punct ";" | .punct ")" | .eof =>
      return .yield none delegated
    | _ =>
      return .yield (some (← parseAssignmentM)) delegated
  if (← consumeKeyword? "new") then
    let callee <- parsePostfixM
    let args <- if (← consumePunct? "(") then parseExprListUntil ")" else pure []
    return .new callee args
  parsePostfixM

private partial def parseExponentM : ParserM Expr := do
  let lhs <- parseUnaryM
  if (← consumePunct? "**") then
    pure (.binary .exp lhs (← parseExponentM))
  else
    pure lhs

private partial def parseMultiplicativeM : ParserM Expr := do
  let lhs <- parseExponentM
  let rec loop (acc : Expr) : ParserM Expr := do
    if (← consumePunct? "*") then
      let rhs <- parseExponentM
      loop (.binary .mul acc rhs)
    else if (← consumePunct? "/") then
      let rhs <- parseExponentM
      loop (.binary .div acc rhs)
    else if (← consumePunct? "%") then
      let rhs <- parseExponentM
      loop (.binary .mod acc rhs)
    else
      pure acc
  loop lhs

private partial def parseAdditiveM : ParserM Expr := do
  let lhs <- parseMultiplicativeM
  let rec loop (acc : Expr) : ParserM Expr := do
    if (← consumePunct? "+") then
      let rhs <- parseMultiplicativeM
      loop (.binary .add acc rhs)
    else if (← consumePunct? "-") then
      let rhs <- parseMultiplicativeM
      loop (.binary .sub acc rhs)
    else
      pure acc
  loop lhs

private partial def parseShiftM : ParserM Expr := do
  let lhs <- parseAdditiveM
  let rec loop (acc : Expr) : ParserM Expr := do
    if (← consumePunct? "<<") then
      let rhs <- parseAdditiveM
      loop (.binary .shl acc rhs)
    else if (← consumePunct? ">>>") then
      let rhs <- parseAdditiveM
      loop (.binary .ushr acc rhs)
    else if (← consumePunct? ">>") then
      let rhs <- parseAdditiveM
      loop (.binary .shr acc rhs)
    else
      pure acc
  loop lhs

private partial def parseRelationalM : ParserM Expr := do
  let lhs <- parseShiftM
  let rec loop (acc : Expr) : ParserM Expr := do
    if (← consumePunct? "<=") then
      let rhs <- parseShiftM
      loop (.binary .le acc rhs)
    else if (← consumePunct? ">=") then
      let rhs <- parseShiftM
      loop (.binary .ge acc rhs)
    else if (← consumePunct? "<") then
      let rhs <- parseShiftM
      loop (.binary .lt acc rhs)
    else if (← consumePunct? ">") then
      let rhs <- parseShiftM
      loop (.binary .gt acc rhs)
    else if (← consumeKeyword? "in") then
      let rhs <- parseShiftM
      loop (.binary .in acc rhs)
    else if (← consumeKeyword? "instanceof") then
      let rhs <- parseShiftM
      loop (.binary .instanceof acc rhs)
    else
      pure acc
  loop lhs

private partial def parseEqualityM : ParserM Expr := do
  let lhs <- parseRelationalM
  let rec loop (acc : Expr) : ParserM Expr := do
    if (← consumePunct? "===") then
      let rhs <- parseRelationalM
      loop (.binary .strictEq acc rhs)
    else if (← consumePunct? "!==") then
      let rhs <- parseRelationalM
      loop (.binary .strictNeq acc rhs)
    else if (← consumePunct? "==") then
      let rhs <- parseRelationalM
      loop (.binary .eq acc rhs)
    else if (← consumePunct? "!=") then
      let rhs <- parseRelationalM
      loop (.binary .neq acc rhs)
    else
      pure acc
  loop lhs

private partial def parseBitAndM : ParserM Expr := do
  let lhs <- parseEqualityM
  let rec loop (acc : Expr) : ParserM Expr := do
    if (← consumePunct? "&") then
      let rhs <- parseEqualityM
      loop (.binary .bitAnd acc rhs)
    else
      pure acc
  loop lhs

private partial def parseBitXorM : ParserM Expr := do
  let lhs <- parseBitAndM
  let rec loop (acc : Expr) : ParserM Expr := do
    if (← consumePunct? "^") then
      let rhs <- parseBitAndM
      loop (.binary .bitXor acc rhs)
    else
      pure acc
  loop lhs

private partial def parseBitOrM : ParserM Expr := do
  let lhs <- parseBitXorM
  let rec loop (acc : Expr) : ParserM Expr := do
    if (← consumePunct? "|") then
      let rhs <- parseBitXorM
      loop (.binary .bitOr acc rhs)
    else
      pure acc
  loop lhs

private partial def parseNullishM : ParserM Expr := do
  let lhs <- parseBitOrM
  let rec loop (acc : Expr) : ParserM Expr := do
    if (← consumePunct? "??") then
      let rhs <- parseBitOrM
      loop (.binary .nullishCoalesce acc rhs)
    else
      pure acc
  loop lhs

private partial def parseLogicalAndM : ParserM Expr := do
  let lhs <- parseNullishM
  let rec loop (acc : Expr) : ParserM Expr := do
    if (← consumePunct? "&&") then
      let rhs <- parseNullishM
      loop (.binary .logAnd acc rhs)
    else
      pure acc
  loop lhs

private partial def parseLogicalOrM : ParserM Expr := do
  let lhs <- parseLogicalAndM
  let rec loop (acc : Expr) : ParserM Expr := do
    if (← consumePunct? "||") then
      let rhs <- parseLogicalAndM
      loop (.binary .logOr acc rhs)
    else
      pure acc
  loop lhs

private partial def parseConditionalM : ParserM Expr := do
  let cond <- parseLogicalOrM
  if (← consumePunct? "?") then
    let thenE <- parseAssignmentM
    expectPunct ":"
    let elseE <- parseAssignmentM
    pure (.conditional cond thenE elseE)
  else
    pure cond

private partial def parseAssignOp? : ParserM (Option AssignOp) := do
  let t <- peek
  match t.kind with
  | .punct "=" => let _ <- bump; pure (some .assign)
  | .punct "+=" => let _ <- bump; pure (some .addAssign)
  | .punct "-=" => let _ <- bump; pure (some .subAssign)
  | .punct "*=" => let _ <- bump; pure (some .mulAssign)
  | .punct "/=" => let _ <- bump; pure (some .divAssign)
  | .punct "%=" => let _ <- bump; pure (some .modAssign)
  | .punct "**=" => let _ <- bump; pure (some .expAssign)
  | .punct "<<=" => let _ <- bump; pure (some .shlAssign)
  | .punct ">>=" => let _ <- bump; pure (some .shrAssign)
  | .punct ">>>=" => let _ <- bump; pure (some .ushrAssign)
  | .punct "&=" => let _ <- bump; pure (some .bitAndAssign)
  | .punct "|=" => let _ <- bump; pure (some .bitOrAssign)
  | .punct "^=" => let _ <- bump; pure (some .bitXorAssign)
  | .punct "&&=" => let _ <- bump; pure (some .logAndAssign)
  | .punct "||=" => let _ <- bump; pure (some .logOrAssign)
  | .punct "??=" => let _ <- bump; pure (some .nullishAssign)
  | _ => pure none

private partial def parseArrowFromSingleIdent? : ParserM (Option Expr) := do
  let t0 <- peekN 0
  let t1 <- peekN 1
  match t0.kind, t1.kind with
  | .ident name, .punct "=>" =>
    let _ <- bump
    let _ <- bump
    let body <-
      if (← consumePunct? "{") then
        let st <- get
        set { st with pos := st.pos - 1 }
        .block <$> parseFunctionBody
      else
        .expr <$> parseAssignmentM
    pure (some (.arrowFunction [parsePatternFromIdent name] body))
  | _, _ => pure none

private partial def parseArrowFromParenParams? : ParserM (Option Expr) := do
  let st0 <- get
  try
    if !(← consumePunct? "(") then
      pure none
    else
      let params <- parseParamListAfterOpen
      expectPunct "=>"
      let body <-
        if (← consumePunct? "{") then
          let st <- get
          set { st with pos := st.pos - 1 }
          .block <$> parseFunctionBody
        else
          .expr <$> parseAssignmentM
      pure (some (.arrowFunction params body))
  catch _ =>
    set st0
    pure none

private partial def parseAssignmentM : ParserM Expr := do
  skipNewlines
  match (← parseArrowFromParenParams?) with
  | some f => pure f
  | none =>
    match (← parseArrowFromSingleIdent?) with
    | some f => pure f
    | none =>
      let lhs <- parseConditionalM
      match (← parseAssignOp?) with
      | none => pure lhs
      | some op =>
        match asAssignTarget lhs with
        | none =>
          throw "Invalid assignment target"
        | some target =>
          let rhs <- parseAssignmentM
          pure (.assign op target rhs)

private partial def parseExprM : ParserM Expr := do
  skipNewlines
  let first <- parseAssignmentM
  let rec loop (acc : List Expr) : ParserM Expr := do
    skipNewlines
    if (← consumePunct? ",") then
      skipNewlines
      let e <- parseAssignmentM
      loop (e :: acc)
    else
      match acc.reverse with
      | [single] => pure single
      | many => pure (.sequence many)
  loop [first]

end

private partial def parseVarDecl : ParserM VarDeclarator := do
  let pat <- parseBindingPatternM
  let init <-
    if (← consumePunct? "=") then
      some <$> parseAssignmentM
    else
      pure none
  pure (.mk pat init)

private partial def parseVarDecls : ParserM (List VarDeclarator) := do
  let first <- parseVarDecl
  let rec loop (acc : List VarDeclarator) : ParserM (List VarDeclarator) := do
    if (← consumePunct? ",") then
      let d <- parseVarDecl
      loop (d :: acc)
    else
      pure acc.reverse
  loop [first]

private def expectStringLit : ParserM String := do
  let t <- peek
  match t.kind with
  | .string s =>
    let _ <- bump
    pure s
  | _ => failExpected "string literal"

private partial def parseImportNamedSpecifiers : ParserM (List ImportSpecifier) := do
  expectPunct "{"
  skipNewlines
  if (← consumePunct? "}") then
    pure []
  else
    let imported <- parseIdentLike
    let localName <- if (← consumeWord? "as") then parseIdentLike else pure imported
    let first : ImportSpecifier := .named imported localName
    let rec loop (acc : List ImportSpecifier) : ParserM (List ImportSpecifier) := do
      skipNewlines
      if (← consumePunct? ",") then
        skipNewlines
        if (← consumePunct? "}") then
          pure acc.reverse
        else
          let i <- parseIdentLike
          let l <- if (← consumeWord? "as") then parseIdentLike else pure i
          loop (.named i l :: acc)
      else
        expectPunct "}"
        pure acc.reverse
    loop [first]

private partial def parseImportSpecifiers : ParserM (List ImportSpecifier) := do
  if (← consumePunct? "*") then
    expectWord "as"
    pure [ .namespace (← parseIdentLike) ]
  else if (← consumePunct? "{") then
    let st <- get
    set { st with pos := st.pos - 1 }
    parseImportNamedSpecifiers
  else
    let defaultName <- parseIdentLike
    let defaultSpec : ImportSpecifier := .default_ defaultName
    if (← consumePunct? ",") then
      if (← consumePunct? "*") then
        expectWord "as"
        pure [defaultSpec, .namespace (← parseIdentLike)]
      else if (← consumePunct? "{") then
        let st <- get
        set { st with pos := st.pos - 1 }
        pure (defaultSpec :: (← parseImportNamedSpecifiers))
      else
        failExpected "import clause"
    else
      pure [defaultSpec]

private def parseForLHSFromExpr (e : Expr) : Except String ForLHS :=
  match parsePatternFromExpr e with
  | some p => pure (.pattern p)
  | none => .error "Invalid for-in/of left-hand side"

private def parseForLHSFromDecls (kind : VarKind) (decls : List VarDeclarator) : Except String ForLHS :=
  match decls with
  | [ .mk pat _ ] => pure (.varDecl kind pat)
  | _ => .error "for-in/of with declarations requires exactly one binding"

mutual

private partial def parseBlockStmt : ParserM Stmt := do
  expectPunct "{"
  let rec gather (acc : List Stmt) : ParserM (List Stmt) := do
    skipSeparators
    if (← consumePunct? "}") then
      pure acc.reverse
    else
      let s <- parseStmt
      gather (s :: acc)
  pure (.block (← gather []))

private partial def parseCaseBody : ParserM (List Stmt) := do
  let rec gather (acc : List Stmt) : ParserM (List Stmt) := do
    skipSeparators
    let t <- peek
    if tokenIsPunct t "}" || tokenIsKeyword t "case" || tokenIsKeyword t "default" then
      pure acc.reverse
    else
      let s <- parseStmt
      gather (s :: acc)
  gather []

private partial def parseSwitchCases : ParserM (List SwitchCase) := do
  let rec gather (acc : List SwitchCase) : ParserM (List SwitchCase) := do
    skipSeparators
    if (← consumePunct? "}") then
      pure acc.reverse
    else if (← consumeKeyword? "case") then
      let test <- parseExprM
      expectPunct ":"
      let body <- parseCaseBody
      gather (.case_ test body :: acc)
    else if (← consumeKeyword? "default") then
      expectPunct ":"
      let body <- parseCaseBody
      gather (.default_ body :: acc)
    else
      failExpected "switch case"
  gather []

private partial def parseForStmt : ParserM Stmt := do
  expectKeyword "for"
  let asyncForOf <- consumeKeyword? "await"
  expectPunct "("
  if (← consumePunct? ";") then
    let cond <- if (← consumePunct? ";") then pure none else (some <$> parseExprM <* expectPunct ";")
    let update <- if (← consumePunct? ")") then pure none else (some <$> parseExprM <* expectPunct ")")
    let body <- parseStmt
    pure (.for none cond update body)
  else if (← consumeKeyword? "var") then
    let decls <- parseVarDecls
    if (← consumeKeyword? "in") then
      let rhs <- parseExprM
      expectPunct ")"
      let lhs <- liftExcept (parseForLHSFromDecls .var decls)
      let body <- parseStmt
      pure (.forIn (some .var) lhs rhs body)
    else if (← consumeKeyword? "of") then
      let rhs <- parseExprM
      expectPunct ")"
      let lhs <- liftExcept (parseForLHSFromDecls .var decls)
      let body <- parseStmt
      if asyncForOf then
        pure (.forOfEx (some .var) lhs rhs body .async)
      else
        pure (.forOf (some .var) lhs rhs body)
    else
      expectPunct ";"
      let cond <- if (← consumePunct? ";") then pure none else (some <$> parseExprM <* expectPunct ";")
      let update <- if (← consumePunct? ")") then pure none else (some <$> parseExprM <* expectPunct ")")
      let body <- parseStmt
      pure (.for (some (.varDecl .var decls)) cond update body)
  else if (← consumeKeyword? "let") then
    let decls <- parseVarDecls
    if (← consumeKeyword? "in") then
      let rhs <- parseExprM
      expectPunct ")"
      let lhs <- liftExcept (parseForLHSFromDecls .let_ decls)
      let body <- parseStmt
      pure (.forIn (some .let_) lhs rhs body)
    else if (← consumeKeyword? "of") then
      let rhs <- parseExprM
      expectPunct ")"
      let lhs <- liftExcept (parseForLHSFromDecls .let_ decls)
      let body <- parseStmt
      if asyncForOf then
        pure (.forOfEx (some .let_) lhs rhs body .async)
      else
        pure (.forOf (some .let_) lhs rhs body)
    else
      expectPunct ";"
      let cond <- if (← consumePunct? ";") then pure none else (some <$> parseExprM <* expectPunct ";")
      let update <- if (← consumePunct? ")") then pure none else (some <$> parseExprM <* expectPunct ")")
      let body <- parseStmt
      pure (.for (some (.varDecl .let_ decls)) cond update body)
  else if (← consumeKeyword? "const") then
    let decls <- parseVarDecls
    if (← consumeKeyword? "in") then
      let rhs <- parseExprM
      expectPunct ")"
      let lhs <- liftExcept (parseForLHSFromDecls .const_ decls)
      let body <- parseStmt
      pure (.forIn (some .const_) lhs rhs body)
    else if (← consumeKeyword? "of") then
      let rhs <- parseExprM
      expectPunct ")"
      let lhs <- liftExcept (parseForLHSFromDecls .const_ decls)
      let body <- parseStmt
      if asyncForOf then
        pure (.forOfEx (some .const_) lhs rhs body .async)
      else
        pure (.forOf (some .const_) lhs rhs body)
    else
      expectPunct ";"
      let cond <- if (← consumePunct? ";") then pure none else (some <$> parseExprM <* expectPunct ";")
      let update <- if (← consumePunct? ")") then pure none else (some <$> parseExprM <* expectPunct ")")
      let body <- parseStmt
      pure (.for (some (.varDecl .const_ decls)) cond update body)
  else
    let initExpr <- parseExprM
    if (← consumeKeyword? "in") then
      let rhs <- parseExprM
      expectPunct ")"
      let lhs <- liftExcept (parseForLHSFromExpr initExpr)
      let body <- parseStmt
      pure (.forIn none lhs rhs body)
    else if (← consumeKeyword? "of") then
      let rhs <- parseExprM
      expectPunct ")"
      let lhs <- liftExcept (parseForLHSFromExpr initExpr)
      let body <- parseStmt
      if asyncForOf then
        pure (.forOfEx none lhs rhs body .async)
      else
        pure (.forOf none lhs rhs body)
    else
      expectPunct ";"
      let cond <- if (← consumePunct? ";") then pure none else (some <$> parseExprM <* expectPunct ";")
      let update <- if (← consumePunct? ")") then pure none else (some <$> parseExprM <* expectPunct ")")
      let body <- parseStmt
      pure (.for (some (.expr initExpr)) cond update body)

private partial def parseFunctionDecl (isAsync : Bool) : ParserM Stmt := do
  expectKeyword "function"
  let isGenerator <- consumePunct? "*"
  let name <- expectIdent
  let params <- parseParamList
  let body <- match (← parseBlockStmt) with
    | .block stmts => pure stmts
    | _ => throw "internal parser error: block expected"
  pure (.functionDecl name params body isAsync isGenerator)

private partial def parseClassDecl : ParserM Stmt := do
  expectKeyword "class"
  let name <- expectIdent
  let superClass <- if (← consumeKeyword? "extends") then some <$> parseExprM else pure none
  let body <- parseClassBody
  pure (.classDecl name superClass body)

private partial def parseStmt : ParserM Stmt := do
  skipSeparators
  let t <- peek
  match t.kind with
  | .eof => failExpected "statement"
  | .punct "{" => parseBlockStmt
  | .punct ";" =>
    let _ <- bump
    pure .empty
  | .kw "if" =>
    let _ <- bump
    expectPunct "("
    let cond <- parseExprM
    expectPunct ")"
    let thenS <- parseStmt
    let elseS <- if (← consumeKeyword? "else") then some <$> parseStmt else pure none
    pure (.if cond thenS elseS)
  | .kw "while" =>
    let _ <- bump
    expectPunct "("
    let cond <- parseExprM
    expectPunct ")"
    pure (.while_ cond (← parseStmt))
  | .kw "do" =>
    let _ <- bump
    let body <- parseStmt
    expectKeyword "while"
    expectPunct "("
    let cond <- parseExprM
    expectPunct ")"
    parseSemiOpt
    pure (.doWhile body cond)
  | .kw "for" =>
    parseForStmt
  | .kw "switch" =>
    let _ <- bump
    expectPunct "("
    let disc <- parseExprM
    expectPunct ")"
    expectPunct "{"
    let cases <- parseSwitchCases
    pure (.switch disc cases)
  | .kw "try" =>
    let _ <- bump
    let body <-
      match (← parseBlockStmt) with
      | .block xs => pure xs
      | _ => throw "internal parser error: block expected"
    skipNewlines
    let catchClause <-
      if (← consumeKeyword? "catch") then
        let param <-
          if (← consumePunct? "(") then
            if (← consumePunct? ")") then
              pure none
            else
              let p <- parseBindingPatternM
              expectPunct ")"
              pure (some p)
          else
            pure none
        let catchBody <-
          match (← parseBlockStmt) with
          | .block xs => pure xs
          | _ => throw "internal parser error: block expected"
        pure (some (.mk param catchBody))
      else
        pure none
    skipNewlines
    let finallyBody <-
      if (← consumeKeyword? "finally") then
        match (← parseBlockStmt) with
        | .block xs => pure (some xs)
        | _ => throw "internal parser error: block expected"
      else
        pure none
    if catchClause.isNone && finallyBody.isNone then
      throw "`try` must have catch or finally"
    pure (.try body catchClause finallyBody)
  | .kw "throw" =>
    let _ <- bump
    let next <- peek
    match next.kind with
    | .newline => throw "Illegal newline after throw"
    | _ =>
      let e <- parseExprM
      parseSemiOpt
      pure (.throw e)
  | .kw "return" =>
    let _ <- bump
    let next <- peek
    match next.kind with
    | .newline | .punct ";" | .punct "}" | .eof =>
      pure (.return none)
    | _ =>
      let e <- parseExprM
      parseSemiOpt
      pure (.return (some e))
  | .kw "break" =>
    let _ <- bump
    let label <- (do
      let nxt <- peek
      match nxt.kind with
      | .ident n => let _ <- bump; pure (some n)
      | _ => pure none)
    parseSemiOpt
    pure (.break label)
  | .kw "continue" =>
    let _ <- bump
    let label <- (do
      let nxt <- peek
      match nxt.kind with
      | .ident n => let _ <- bump; pure (some n)
      | _ => pure none)
    parseSemiOpt
    pure (.continue label)
  | .kw "debugger" =>
    let _ <- bump
    parseSemiOpt
    pure .debugger
  | .kw "with" =>
    let _ <- bump
    expectPunct "("
    let obj <- parseExprM
    expectPunct ")"
    pure (.with obj (← parseStmt))
  | .kw "function" =>
    parseFunctionDecl false
  | .kw "class" =>
    parseClassDecl
  | .kw "async" =>
    let t1 <- peekN 1
    if tokenIsKeyword t1 "function" then
      let _ <- bump
      parseFunctionDecl true
    else
      let e <- parseExprM
      parseSemiOpt
      pure (.expr e)
  | .kw "var" =>
    let _ <- bump
    let decls <- parseVarDecls
    parseSemiOpt
    pure (.varDecl .var decls)
  | .kw "let" =>
    let _ <- bump
    let decls <- parseVarDecls
    parseSemiOpt
    pure (.varDecl .let_ decls)
  | .kw "const" =>
    let _ <- bump
    let decls <- parseVarDecls
    parseSemiOpt
    pure (.varDecl .const_ decls)
  | .kw "import" =>
    let _ <- bump
    let importStmt <- parseImportDeclStmt
    parseSemiOpt
    pure importStmt
  | .kw "export" =>
    let _ <- bump
    if (← consumeKeyword? "default") then
      let e <- parseExprM
      parseSemiOpt
      pure (.export_ (.default_ e))
    else if (← consumePunct? "*") then
      let alias_ <-
        if (← consumeWord? "as") then
          some <$> parseIdentLike
        else
          pure none
      expectWord "from"
      let source <- (do
        let tk <- peek
        match tk.kind with
        | .string s => let _ <- bump; pure s
        | _ => throw "Expected export source string literal")
      parseSemiOpt
      pure (.export_ (.all source alias_))
    else if (← consumePunct? "{") then
      let rec parseSpecs (acc : List ExportSpecifier) : ParserM (List ExportSpecifier) := do
        if (← consumePunct? "}") then
          pure acc.reverse
        else
          let localName <- parseIdentLike
          let exportedName <-
            if (← consumeWord? "as") then
              parseIdentLike
            else
              pure localName
          let spec := ExportSpecifier.mk localName exportedName
          if (← consumePunct? ",") then
            if (← consumePunct? "}") then
              pure (List.reverse (spec :: acc))
            else
              parseSpecs (spec :: acc)
          else
            expectPunct "}"
            pure (List.reverse (spec :: acc))
      let specs <- parseSpecs []
      let source <-
        if (← consumeWord? "from") then
          let tk <- peek
          match tk.kind with
          | .string s => let _ <- bump; pure (some s)
          | _ => throw "Expected export source string literal"
        else
          pure none
      parseSemiOpt
      pure (.export_ (.named specs source))
    else
      let next <- peek
      match next.kind with
      | .kw "var" =>
        let _ <- bump
        let decls <- parseVarDecls
        parseSemiOpt
        pure (.export_ (.decl (.varDecl .var decls)))
      | .kw "let" =>
        let _ <- bump
        let decls <- parseVarDecls
        parseSemiOpt
        pure (.export_ (.decl (.varDecl .let_ decls)))
      | .kw "const" =>
        let _ <- bump
        let decls <- parseVarDecls
        parseSemiOpt
        pure (.export_ (.decl (.varDecl .const_ decls)))
      | .kw "function" =>
        pure (.export_ (.decl (← parseFunctionDecl false)))
      | .kw "class" =>
        pure (.export_ (.decl (← parseClassDecl)))
      | .kw "async" =>
        let t1 <- peekN 1
        if tokenIsKeyword t1 "function" then
          let _ <- bump
          pure (.export_ (.decl (← parseFunctionDecl true)))
        else
          let e <- parseExprM
          parseSemiOpt
          pure (.export_ (.default_ e))
      | _ =>
        let e <- parseExprM
        parseSemiOpt
        pure (.export_ (.default_ e))
  | _ =>
    let e <- parseExprM
    if (← consumePunct? ":") then
      match e with
      | .ident label =>
        pure (.labeled label (← parseStmt))
      | _ => throw "Invalid label"
    else
      parseSemiOpt
      pure (.expr e)

end

private partial def parseProgram : ParserM Program := do
  let rec gather (acc : List Stmt) : ParserM (List Stmt) := do
    skipSeparators
    let t <- peek
    match t.kind with
    | .eof => pure acc.reverse
    | _ =>
      let s <- parseStmt
      gather (s :: acc)
  pure (.script (← gather []))

/-- Parse a JavaScript source string into a Program AST. -/
def parse (source : String) : Except String Program := do
  let toks <- tokenize source
  let init : ParserState := { tokens := toks.toArray, pos := 0 }
  (parseProgram.run init).map Prod.fst

/-- Parse a single expression and reject trailing tokens. -/
def parseExpr (source : String) : Except String Expr := do
  let toks <- tokenize source
  let init : ParserState := { tokens := toks.toArray, pos := 0 }
  let (e, st) <- (parseExprM.run init)
  let ((), st2) <- (skipSeparators.run st)
  let trailing := st2.tokens.getD st2.pos eofTok
  match trailing.kind with
  | .eof => pure e
  | _ => throw s!"Unexpected trailing token {tokenDesc trailing} at {trailing.pos.line}:{trailing.pos.col}"

end VerifiedJS.Source
