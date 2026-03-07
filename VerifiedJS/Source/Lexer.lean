/-
  VerifiedJS — JavaScript Lexer
  Context-sensitive lexer: `/` is division or regex depending on prior token.
  Outside the verified TCB.
-/

namespace VerifiedJS.Source

/-- Token types for JavaScript lexing -/
inductive TokenKind where
  -- Literals
  | number (n : Float)
  | string (s : String)
  | template (parts : List String)
  | regex (pattern flags : String)
  | ident (name : String)
  -- Keywords
  | kw (name : String)
  -- Punctuation
  | punct (s : String)
  -- Special
  | eof
  | newline
  deriving Repr, BEq

structure SourcePos where
  line : Nat
  col : Nat
  offset : Nat
  deriving Repr, BEq

structure Token where
  kind : TokenKind
  pos : SourcePos
  deriving Repr

/-- Lexer state — tracks whether `/` should be interpreted as division or regex start -/
structure LexerState where
  source : String
  pos : Nat
  line : Nat
  col : Nat
  /-- True when the next `/` should be interpreted as regex -/
  expectRegex : Bool
  deriving Repr

/-- Initialize a lexer from source text -/
def LexerState.init (source : String) : LexerState :=
  { source, pos := 0, line := 1, col := 1, expectRegex := true }

/-- Internal lexer position update helper. -/
private def advancePos (line col offset : Nat) (c : Char) : Nat × Nat × Nat :=
  if c = '\n' then
    (line + 1, 1, offset + 1)
  else
    (line, col + 1, offset + 1)

private def isIdentStart (c : Char) : Bool :=
  c.isAlpha || c = '_' || c = '$'

private def isIdentContinue (c : Char) : Bool :=
  isIdentStart c || c.isDigit

private def keywordSet : List String :=
  [ "break", "case", "catch", "class", "const", "continue", "debugger", "default"
  , "delete", "do", "else", "export", "extends", "finally", "for", "function", "if"
  , "import", "in", "instanceof", "let", "new", "return", "switch", "this", "throw"
  , "try", "typeof", "var", "void", "while", "with", "yield", "await", "true", "false"
  , "null", "undefined"
  ]

private def isKeyword (s : String) : Bool :=
  keywordSet.contains s

private def tokenCanEndExpression : TokenKind → Bool
  | .number _ | .string _ | .regex _ _ | .ident _ => true
  | .kw k => k = "this" || k = "true" || k = "false" || k = "null" || k = "undefined"
  | .punct p => p = ")" || p = "]" || p = "}" || p = "++" || p = "--"
  | _ => false

private def skipLineComment (chars : List Char) : List Char × Nat :=
  let rec go (rest : List Char) (consumed : Nat) :=
    match rest with
    | [] => ([], consumed)
    | '\n' :: _ => (rest, consumed)
    | _ :: cs => go cs (consumed + 1)
  go chars 0

private def skipBlockComment (chars : List Char) (line col offset consumed : Nat) :
    Except String (List Char × Nat × Nat × Nat × Nat) := do
  let rec go (rest : List Char) (ln cl off cons : Nat) :
      Except String (List Char × Nat × Nat × Nat × Nat) := do
    match rest with
    | [] => throw s!"Lexer error at {ln}:{cl}: unterminated block comment"
    | '*' :: '/' :: tail =>
      let (_, cl1, off1) := advancePos ln cl off '*'
      let (_, cl2, off2) := advancePos ln cl1 off1 '/'
      pure (tail, ln, cl2, off2, cons + 2)
    | c :: tail =>
      let (ln', cl', off') := advancePos ln cl off c
      go tail ln' cl' off' (cons + 1)
  go chars line col offset consumed

private def readWhile (chars : List Char) (p : Char → Bool) :
    List Char × List Char :=
  let rec go (rest acc : List Char) :=
    match rest with
    | c :: cs =>
      if p c then
        go cs (c :: acc)
      else
        (acc.reverse, rest)
    | [] => (acc.reverse, [])
  go chars []

private def readStringBody (quote : Char) (chars : List Char) :
    String × List Char × Nat :=
  let rec go (rest acc : List Char) (consumed : Nat) :=
    match rest with
    | [] => (String.mk acc.reverse, [], consumed)
    | '\\' :: c :: cs => go cs (c :: '\\' :: acc) (consumed + 2)
    | c :: cs =>
      if c = quote then
        (String.mk acc.reverse, cs, consumed + 1)
      else
        go cs (c :: acc) (consumed + 1)
  go chars [] 0

private def readRegexBody (chars : List Char) : String × String × List Char × Nat :=
  let rec body (rest acc : List Char) (consumed : Nat) :=
    match rest with
    | [] => (String.mk acc.reverse, "", [], consumed)
    | '\\' :: c :: cs => body cs (c :: '\\' :: acc) (consumed + 2)
    | '/' :: cs =>
      let (flagsChars, tail) := readWhile cs (fun c => c.isAlpha)
      let flags := String.mk flagsChars
      let consumedFlags := flagsChars.length + 1
      (String.mk acc.reverse, flags, tail, consumed + consumedFlags)
    | c :: cs => body cs (c :: acc) (consumed + 1)
  body chars [] 0

private def punct2Set : List String :=
  [ "==", "!=", "<=", ">=", "&&", "||", "??", "=>", "++", "--"
  , "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<", ">>", "**"
  , "?."
  ]

private def punct3Set : List String := ["===", "!==", "<<=", ">>=", "**=", ">>>", ">>>="]

private def readPunct (chars : List Char) : String × List Char :=
  match chars with
  | a :: b :: c :: rest =>
    let s3 := String.mk [a, b, c]
    if punct3Set.contains s3 then
      (s3, rest)
    else
      let s2 := String.mk [a, b]
      if punct2Set.contains s2 then
        (s2, c :: rest)
      else
        (String.mk [a], b :: c :: rest)
  | a :: b :: rest =>
    let s2 := String.mk [a, b]
    if punct2Set.contains s2 then
      (s2, rest)
    else
      (String.mk [a], b :: rest)
  | a :: rest => (String.mk [a], rest)
  | [] => ("", [])

/-- Tokenize the full source string. -/
partial def tokenizeChars
    (chars : List Char)
    (line col offset : Nat)
    (expectRegex : Bool)
    (acc : List Token) : Except String (List Token) := do
  match chars with
  | [] =>
    return (acc.reverse ++ [{ kind := .eof, pos := { line, col, offset } }])
  | c :: cs =>
    if c = ' ' || c = '\t' || c = '\r' then
      let (_, nextCol, nextOffset) := advancePos line col offset c
      tokenizeChars cs line nextCol nextOffset expectRegex acc
    else if c = '\n' then
      let tok : Token := { kind := .newline, pos := { line, col, offset } }
      let (nextLine, nextCol, nextOffset) := advancePos line col offset c
      tokenizeChars cs nextLine nextCol nextOffset true (tok :: acc)
    else if isIdentStart c then
      let (idChars, rest) := readWhile (c :: cs) isIdentContinue
      let s := String.mk idChars
      let kind := if isKeyword s then TokenKind.kw s else TokenKind.ident s
      let tok : Token := { kind, pos := { line, col, offset } }
      tokenizeChars rest line (col + idChars.length) (offset + idChars.length)
        (not (tokenCanEndExpression kind)) (tok :: acc)
    else if c.isDigit then
      let (numChars, rest) := readWhile (c :: cs) (fun ch => ch.isDigit || ch = '.')
      let n := (String.toNat? (String.mk numChars)).getD 0
      let tok : Token := { kind := .number (Float.ofNat n), pos := { line, col, offset } }
      tokenizeChars rest line (col + numChars.length) (offset + numChars.length) false (tok :: acc)
    else if c = '"' || c = '\'' then
      let (body, rest, consumedTail) := readStringBody c cs
      let tok : Token := { kind := .string body, pos := { line, col, offset } }
      let consumed := consumedTail + 1
      tokenizeChars rest line (col + consumed) (offset + consumed) false (tok :: acc)
    else if c = '/' then
      match cs with
      | '/' :: tail =>
        let (rest, consumedComment) := skipLineComment tail
        let consumed := consumedComment + 2
        tokenizeChars rest line (col + consumed) (offset + consumed) expectRegex acc
      | '*' :: tail =>
        let (rest, line', col', offset', _) ← skipBlockComment tail line (col + 2) (offset + 2) 2
        tokenizeChars rest line' col' offset' expectRegex acc
      | '=' :: tail =>
        let tok : Token := { kind := .punct "/=", pos := { line, col, offset } }
        tokenizeChars tail line (col + 2) (offset + 2) true (tok :: acc)
      | _ =>
        if expectRegex then
        let (pat, flags, rest, consumedTail) := readRegexBody cs
        let tok : Token := { kind := .regex pat flags, pos := { line, col, offset } }
        let consumed := consumedTail + 1
        tokenizeChars rest line (col + consumed) (offset + consumed) false (tok :: acc)
        else
          let tok : Token := { kind := .punct "/", pos := { line, col, offset } }
          tokenizeChars cs line (col + 1) (offset + 1) true (tok :: acc)
    else
      let (p, rest) := readPunct (c :: cs)
      if p.isEmpty then
        throw s!"Lexer error at {line}:{col}: unexpected end of input"
      else
        let kind : TokenKind := .punct p
        let tok : Token := { kind, pos := { line, col, offset } }
        tokenizeChars rest line (col + p.length) (offset + p.length)
          (not (tokenCanEndExpression kind)) (tok :: acc)

/-- Tokenize the full source string -/
def tokenize (source : String) : Except String (List Token) :=
  tokenizeChars source.toList 1 1 0 true []

end VerifiedJS.Source
