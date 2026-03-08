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
  | bigint (digits : String)
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
  c.isAlpha || c = '_' || c = '$' || c.toNat > 0x7F

private def isIdentContinue (c : Char) : Bool :=
  isIdentStart c || c.isDigit || c.toNat = 0x200C || c.toNat = 0x200D

private def keywordSet : List String :=
  [ "break", "case", "catch", "class", "const", "continue", "debugger", "default"
  , "delete", "do", "else", "export", "extends", "finally", "for", "function", "if"
  , "import", "in", "instanceof", "let", "new", "of", "return", "switch", "this", "throw"
  , "try", "typeof", "var", "void", "while", "with", "yield", "await", "true", "false"
  , "null", "undefined"
  ]

private def isKeyword (s : String) : Bool :=
  keywordSet.contains s

/--
ECMA-262 §11 lexical grammar is context-sensitive around `/`:
after specific control headers (e.g. `if (...)`) the next token starts a statement,
so `/` should be lexed as a regex literal start rather than division.
-/
private def controlHeaderKeyword (s : String) : Bool :=
  s = "if" || s = "while" || s = "for" || s = "with" || s = "catch"

private def tokenCanEndExpression : TokenKind → Bool
  | .number _ | .bigint _ | .string _ | .regex _ _ | .ident _ => true
  | .kw k => k = "this" || k = "true" || k = "false" || k = "null" || k = "undefined"
  | .punct p => p = ")" || p = "]" || p = "}" || p = "++" || p = "--"
  | _ => false

private def hexDigitVal? (c : Char) : Option Nat :=
  if c.isDigit then
    some (c.toNat - '0'.toNat)
  else if c >= 'a' && c <= 'f' then
    some (10 + (c.toNat - 'a'.toNat))
  else if c >= 'A' && c <= 'F' then
    some (10 + (c.toNat - 'A'.toNat))
  else
    none

private def parseUnicodeEscapeStart? : List Char → Option (Char × List Char × Nat) := fun chars =>
  let parseFixed? : Option (Char × List Char × Nat) :=
    match chars with
    | '\\' :: 'u' :: h1 :: h2 :: h3 :: h4 :: rest =>
        match hexDigitVal? h1, hexDigitVal? h2, hexDigitVal? h3, hexDigitVal? h4 with
        | some v1, some v2, some v3, some v4 =>
            let cp := v1 * 4096 + v2 * 256 + v3 * 16 + v4
            some (Char.ofNat cp, rest, 6)
        | _, _, _, _ => none
    | _ => none
  let parseBraced? : Option (Char × List Char × Nat) :=
    match chars with
    | '\\' :: 'u' :: '{' :: rest =>
        let rec gather (rs : List Char) (acc : Nat) (digits : Nat) : Option (Char × List Char × Nat) :=
          match rs with
          | '}' :: tail =>
              if digits = 0 || acc > 0x10FFFF then
                none
              else
                some (Char.ofNat acc, tail, digits + 4)
          | c :: tail =>
              match hexDigitVal? c with
              | some v => gather tail (acc * 16 + v) (digits + 1)
              | none => none
          | [] => none
        gather rest 0 0
    | _ => none
  match parseBraced? with
  | some r => some r
  | none => parseFixed?

private partial def readIdentifierWithEscapes (chars : List Char) : Option (String × List Char × Nat) :=
  let rec loop (rest accRev : List Char) (consumed : Nat) : Option (String × List Char × Nat) :=
    match rest with
    | c :: cs =>
        if isIdentContinue c then
          loop cs (c :: accRev) (consumed + 1)
        else
          match parseUnicodeEscapeStart? rest with
          | some (escCh, rest', escConsumed) =>
              if isIdentContinue escCh then
                loop rest' (escCh :: accRev) (consumed + escConsumed)
              else
                some (String.mk accRev.reverse, rest, consumed)
          | none =>
              some (String.mk accRev.reverse, rest, consumed)
    | [] =>
        some (String.mk accRev.reverse, [], consumed)
  match chars with
  | c :: cs =>
      if isIdentStart c then
        loop cs [c] 1
      else
        match parseUnicodeEscapeStart? chars with
        | some (firstCh, rest, consumed) =>
            if isIdentStart firstCh then
              loop rest [firstCh] consumed
            else
              none
        | none => none
  | [] => none

private def startsIdentifierWithEscapes (chars : List Char) : Bool :=
  (readIdentifierWithEscapes chars).isSome

private def stripUnderscoresChars (cs : List Char) : List Char :=
  cs.filter (fun c => c != '_')

private def pow10Nat (n : Nat) : Float :=
  (List.replicate n ()).foldl (fun acc _ => acc * 10.0) 1.0

private def parseNatBase? (base : Nat) (cs : List Char) : Option Nat :=
  let rec go (rest : List Char) (acc : Nat) : Option Nat :=
    match rest with
    | [] => some acc
    | c :: tail =>
        let digit? :=
          if c.isDigit then
            some (c.toNat - '0'.toNat)
          else if c >= 'a' && c <= 'f' then
            some (10 + (c.toNat - 'a'.toNat))
          else if c >= 'A' && c <= 'F' then
            some (10 + (c.toNat - 'A'.toNat))
          else
            none
        match digit? with
        | some d =>
            if d < base then
              go tail (acc * base + d)
            else
              none
        | none => none
  go cs 0

private def parseUnsignedDecimal? (cs : List Char) : Option Nat :=
  if cs.isEmpty then
    none
  else
    parseNatBase? 10 cs

private def parseNumberFloat (raw : String) : Float :=
  let s := String.mk (stripUnderscoresChars raw.toList)
  if s.startsWith "0x" || s.startsWith "0X" then
    let hexPart := (s.drop 2).toString.toList
    match parseNatBase? 16 hexPart with
    | some n => Float.ofNat n
    | none => 0.0
  else if s.startsWith "0b" || s.startsWith "0B" then
    let binPart := (s.drop 2).toString.toList
    match parseNatBase? 2 binPart with
    | some n => Float.ofNat n
    | none => 0.0
  else if s.startsWith "0o" || s.startsWith "0O" then
    let octPart := (s.drop 2).toString.toList
    match parseNatBase? 8 octPart with
    | some n => Float.ofNat n
    | none => 0.0
  else
    let expParts := String.splitOn s "e"
    let (mantStr, expStr?) :=
      match expParts with
      | [m, e] => (m, some e)
      | _ =>
          let expPartsUpper := String.splitOn s "E"
          match expPartsUpper with
          | [m, e] => (m, some e)
          | _ => (s, none)
    let mantParts := String.splitOn mantStr "."
    let mantVal :=
      match mantParts with
      | [whole] =>
          match parseUnsignedDecimal? whole.toList with
          | some n => Float.ofNat n
          | none => 0.0
      | [whole, frac] =>
          let wholeVal :=
            match parseUnsignedDecimal? whole.toList with
            | some n => Float.ofNat n
            | none => 0.0
          let fracVal :=
            match parseUnsignedDecimal? frac.toList with
            | some n => Float.ofNat n / pow10Nat frac.length
            | none => 0.0
          wholeVal + fracVal
      | _ => 0.0
    match expStr? with
    | none => mantVal
    | some expRaw =>
        let expSignNeg := expRaw.startsWith "-"
        let expDigits :=
          if expRaw.startsWith "-" || expRaw.startsWith "+" then
            (expRaw.drop 1).toString
          else
            expRaw
        match parseUnsignedDecimal? expDigits.toList with
        | some e =>
            if expSignNeg then
              mantVal / pow10Nat e
            else
              mantVal * pow10Nat e
        | none => mantVal

private def readWhileChars (chars : List Char) (p : Char → Bool) : List Char × List Char :=
  let rec go (rest acc : List Char) :=
    match rest with
    | c :: cs =>
        if p c then
          go cs (c :: acc)
        else
          (acc.reverse, rest)
    | [] => (acc.reverse, [])
  go chars []

private def readNumberLiteral (chars : List Char) : String × List Char :=
  match chars with
  | '0' :: ('x' :: cs) =>
      let (restDigits, rest) := readWhileChars cs (fun ch => ch.isDigit || (ch >= 'a' && ch <= 'f') || (ch >= 'A' && ch <= 'F') || ch = '_')
      ("0x" ++ String.mk restDigits, rest)
  | '0' :: ('X' :: cs) =>
      let (restDigits, rest) := readWhileChars cs (fun ch => ch.isDigit || (ch >= 'a' && ch <= 'f') || (ch >= 'A' && ch <= 'F') || ch = '_')
      ("0X" ++ String.mk restDigits, rest)
  | '0' :: ('b' :: cs) =>
      let (restDigits, rest) := readWhileChars cs (fun ch => ch = '0' || ch = '1' || ch = '_')
      ("0b" ++ String.mk restDigits, rest)
  | '0' :: ('B' :: cs) =>
      let (restDigits, rest) := readWhileChars cs (fun ch => ch = '0' || ch = '1' || ch = '_')
      ("0B" ++ String.mk restDigits, rest)
  | '0' :: ('o' :: cs) =>
      let (restDigits, rest) := readWhileChars cs (fun ch => ((ch >= '0' && ch <= '7') || ch = '_'))
      ("0o" ++ String.mk restDigits, rest)
  | '0' :: ('O' :: cs) =>
      let (restDigits, rest) := readWhileChars cs (fun ch => ((ch >= '0' && ch <= '7') || ch = '_'))
      ("0O" ++ String.mk restDigits, rest)
  | _ =>
      let (intDigits, rest0) := readWhileChars chars (fun ch => ch.isDigit || ch = '_')
      let intPart := String.mk intDigits
      let (fracPart, rest1) :=
        match rest0 with
        | '.' :: tail =>
            let (fracDigits, restTail) := readWhileChars tail (fun ch => ch.isDigit || ch = '_')
            ("." ++ String.mk fracDigits, restTail)
        | _ => ("", rest0)
      let (expPart, rest2) :=
        match rest1 with
        | ('e' :: tail) =>
            let (signPart, tail1) :=
              match tail with
              | ('+' :: more) => ("+", more)
              | ('-' :: more) => ("-", more)
              | _ => ("", tail)
            let (expDigits, restTail) := readWhileChars tail1 (fun ch => ch.isDigit || ch = '_')
            ("e" ++ signPart ++ String.mk expDigits, restTail)
        | ('E' :: tail) =>
            let (signPart, tail1) :=
              match tail with
              | ('+' :: more) => ("+", more)
              | ('-' :: more) => ("-", more)
              | _ => ("", tail)
            let (expDigits, restTail) := readWhileChars tail1 (fun ch => ch.isDigit || ch = '_')
            ("E" ++ signPart ++ String.mk expDigits, restTail)
        | _ => ("", rest1)
      (intPart ++ fracPart ++ expPart, rest2)

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

private def readTemplateBody (chars : List Char) :
    String × List Char × Nat × Bool :=
  let rec go (rest acc : List Char) (consumed : Nat) (escaped : Bool) :=
    match rest with
    | [] => (String.mk acc.reverse, [], consumed, false)
    | c :: cs =>
      if escaped then
        go cs (c :: acc) (consumed + 1) false
      else if c = '\\' then
        go cs (c :: acc) (consumed + 1) true
      else if c = '`' then
        (String.mk acc.reverse, cs, consumed + 1, true)
      else
        go cs (c :: acc) (consumed + 1) false
  go chars [] 0 false

private def readRegexBody (chars : List Char) : String × String × List Char × Nat × Bool :=
  let rec body (rest acc : List Char) (consumed : Nat) (inClass escaped : Bool) :=
    match rest with
    | [] => (String.mk acc.reverse, "", [], consumed, false)
    | '\n' :: _ => (String.mk acc.reverse, "", rest, consumed, false)
    | c :: cs =>
      if escaped then
        body cs (c :: acc) (consumed + 1) inClass false
      else if c = '\\' then
        body cs (c :: acc) (consumed + 1) inClass true
      else if c = '[' then
        body cs (c :: acc) (consumed + 1) true false
      else if c = ']' then
        body cs (c :: acc) (consumed + 1) false false
      else if c = '/' && !inClass then
      let (flagsChars, tail) := readWhile cs (fun c => c.isAlpha)
      let flags := String.mk flagsChars
      let consumedFlags := flagsChars.length + 1
      (String.mk acc.reverse, flags, tail, consumed + consumedFlags, true)
      else
        body cs (c :: acc) (consumed + 1) inClass false
  body chars [] 0 false false

private def punct2Set : List String :=
  [ "==", "!=", "<=", ">=", "&&", "||", "??", "=>", "++", "--"
  , "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<", ">>", "**"
  , "?."
  ]

private def punct3Set : List String :=
  ["===", "!==", "<<=", ">>=", "**=", ">>>", ">>>=", "...", "??=", "&&=", "||="]

private def punct4Set : List String :=
  [">>>="]

private def readPunct (chars : List Char) : String × List Char :=
  match chars with
  | a :: b :: c :: d :: rest =>
    let s4 := String.mk [a, b, c, d]
    if punct4Set.contains s4 then
      (s4, rest)
    else
      let s3 := String.mk [a, b, c]
      if punct3Set.contains s3 then
        (s3, d :: rest)
      else
        let s2 := String.mk [a, b]
        if punct2Set.contains s2 then
          (s2, c :: d :: rest)
        else
          (String.mk [a], b :: c :: d :: rest)
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
    (parenDepth : Nat)
    (controlHeaderParens : List Nat)
    (pendingControlHeader : Bool)
    (braceDepth : Nat)
    (controlBlockBraces : List Nat)
    (pendingControlBlock : Bool)
    (acc : List Token) : Except String (List Token) := do
  match chars with
  | [] =>
    return (acc.reverse ++ [{ kind := .eof, pos := { line, col, offset } }])
  | c :: cs =>
    if c = '#' && line = 1 && col = 1 then
      match cs with
      | '!' :: tail =>
        let (rest, consumedComment) := skipLineComment tail
        let consumed := consumedComment + 2
        tokenizeChars rest line (col + consumed) (offset + consumed) expectRegex parenDepth controlHeaderParens pendingControlHeader braceDepth controlBlockBraces pendingControlBlock acc
      | _ =>
        throw s!"Lexer error at {line}:{col}: unexpected character `#`"
    else if c = '#' then
      match cs with
      | '\\' :: _ =>
        match readIdentifierWithEscapes cs with
        | some (name, rest, consumedIdent) =>
          let hashTok : Token := { kind := .punct "#", pos := { line, col, offset } }
          let identTok : Token := { kind := .ident name, pos := { line, col := col + 1, offset := offset + 1 } }
          let consumed := consumedIdent + 1
          tokenizeChars rest line (col + consumed) (offset + consumed) false parenDepth controlHeaderParens false braceDepth controlBlockBraces false (identTok :: hashTok :: acc)
        | none =>
          throw s!"Lexer error at {line}:{col}: invalid private name escape"
      | _ =>
        let tok : Token := { kind := .punct "#", pos := { line, col, offset } }
        tokenizeChars cs line (col + 1) (offset + 1) true parenDepth controlHeaderParens false braceDepth controlBlockBraces false (tok :: acc)
    else if c = ' ' || c = '\t' || c = '\r' then
      let (_, nextCol, nextOffset) := advancePos line col offset c
      tokenizeChars cs line nextCol nextOffset expectRegex parenDepth controlHeaderParens pendingControlHeader braceDepth controlBlockBraces pendingControlBlock acc
    else if c = '\n' then
      let tok : Token := { kind := .newline, pos := { line, col, offset } }
      let (nextLine, nextCol, nextOffset) := advancePos line col offset c
      tokenizeChars cs nextLine nextCol nextOffset expectRegex parenDepth controlHeaderParens pendingControlHeader braceDepth controlBlockBraces pendingControlBlock (tok :: acc)
    else if startsIdentifierWithEscapes (c :: cs) then
      match readIdentifierWithEscapes (c :: cs) with
      | some (s, rest, consumed) =>
          let kind := if isKeyword s then TokenKind.kw s else TokenKind.ident s
          let tok : Token := { kind, pos := { line, col, offset } }
          let pendingControlHeader' := match kind with
            | .kw k => controlHeaderKeyword k
            | _ => false
          tokenizeChars rest line (col + consumed) (offset + consumed)
            (not (tokenCanEndExpression kind)) parenDepth controlHeaderParens pendingControlHeader' braceDepth controlBlockBraces false (tok :: acc)
      | none =>
          throw s!"Lexer error at {line}:{col}: invalid unicode escape identifier start"
    else if c.isDigit then
      let (numRaw, rest0) := readNumberLiteral (c :: cs)
      let (kind, rest, consumed) :=
        match rest0 with
        | 'n' :: tail =>
            (TokenKind.bigint (String.mk (stripUnderscoresChars numRaw.toList)), tail, numRaw.length + 1)
        | _ =>
            (TokenKind.number (parseNumberFloat numRaw), rest0, numRaw.length)
      let tok : Token := { kind, pos := { line, col, offset } }
      tokenizeChars rest line (col + consumed) (offset + consumed) false parenDepth controlHeaderParens false braceDepth controlBlockBraces false (tok :: acc)
    else if c = '"' || c = '\'' then
      let (body, rest, consumedTail) := readStringBody c cs
      let tok : Token := { kind := .string body, pos := { line, col, offset } }
      let consumed := consumedTail + 1
      tokenizeChars rest line (col + consumed) (offset + consumed) false parenDepth controlHeaderParens false braceDepth controlBlockBraces false (tok :: acc)
    else if c = '`' then
      let (body, rest, consumedTail, terminated) := readTemplateBody cs
      if !terminated then
        throw s!"Lexer error at {line}:{col}: unterminated template literal"
      let tok : Token := { kind := .template [body], pos := { line, col, offset } }
      let consumed := consumedTail + 1
      tokenizeChars rest line (col + consumed) (offset + consumed) false parenDepth controlHeaderParens false braceDepth controlBlockBraces false (tok :: acc)
    else if c = '/' then
      match cs with
      | '/' :: tail =>
        let (rest, consumedComment) := skipLineComment tail
        let consumed := consumedComment + 2
        tokenizeChars rest line (col + consumed) (offset + consumed) expectRegex parenDepth controlHeaderParens pendingControlHeader braceDepth controlBlockBraces pendingControlBlock acc
      | '*' :: tail =>
        let (rest, line', col', offset', _) ← skipBlockComment tail line (col + 2) (offset + 2) 2
        tokenizeChars rest line' col' offset' expectRegex parenDepth controlHeaderParens pendingControlHeader braceDepth controlBlockBraces pendingControlBlock acc
      | '=' :: tail =>
        let tok : Token := { kind := .punct "/=", pos := { line, col, offset } }
        tokenizeChars tail line (col + 2) (offset + 2) true parenDepth controlHeaderParens false braceDepth controlBlockBraces false (tok :: acc)
      | _ =>
        if expectRegex then
        let (pat, flags, rest, consumedTail, terminated) := readRegexBody cs
        if !terminated then
          throw s!"Lexer error at {line}:{col}: unterminated regex literal"
        let tok : Token := { kind := .regex pat flags, pos := { line, col, offset } }
        let consumed := consumedTail + 1
        tokenizeChars rest line (col + consumed) (offset + consumed) false parenDepth controlHeaderParens false braceDepth controlBlockBraces false (tok :: acc)
        else
          let tok : Token := { kind := .punct "/", pos := { line, col, offset } }
          tokenizeChars cs line (col + 1) (offset + 1) true parenDepth controlHeaderParens false braceDepth controlBlockBraces false (tok :: acc)
    else
      let (p, rest) := readPunct (c :: cs)
      if p.isEmpty then
        throw s!"Lexer error at {line}:{col}: unexpected end of input"
      else
        let kind : TokenKind := .punct p
        let tok : Token := { kind, pos := { line, col, offset } }
        let (parenDepth', controlHeaderParens', expectRegex', braceDepth', controlBlockBraces', pendingControlBlock') :=
          if p = "(" then
            let depth' := parenDepth + 1
            let controlHeaderParens' :=
              if pendingControlHeader then depth' :: controlHeaderParens else controlHeaderParens
            (depth', controlHeaderParens', true, braceDepth, controlBlockBraces, false)
          else if p = ")" then
            let closingDepth := parenDepth
            let depth' := parenDepth - 1
            let (controlHeaderParens'', isControlClose) :=
              match controlHeaderParens with
              | hd :: tl =>
                if hd = closingDepth then (tl, true) else (controlHeaderParens, false)
              | [] => ([], false)
            (depth', controlHeaderParens'', isControlClose || not (tokenCanEndExpression kind), braceDepth, controlBlockBraces, isControlClose)
          else if p = "{" then
            let depth' := braceDepth + 1
            let controlBlockBraces' :=
              if pendingControlBlock then depth' :: controlBlockBraces else controlBlockBraces
            (parenDepth, controlHeaderParens, true, depth', controlBlockBraces', false)
          else if p = "}" then
            let closingDepth := braceDepth
            let depth' := braceDepth - 1
            let (controlBlockBraces'', closedControlBlock) :=
              match controlBlockBraces with
              | hd :: tl =>
                if hd = closingDepth then (tl, true) else (controlBlockBraces, false)
              | [] => ([], false)
            (parenDepth, controlHeaderParens, closedControlBlock || not (tokenCanEndExpression kind), depth', controlBlockBraces'', false)
          else
            (parenDepth, controlHeaderParens, not (tokenCanEndExpression kind), braceDepth, controlBlockBraces, false)
        tokenizeChars rest line (col + p.length) (offset + p.length)
          expectRegex' parenDepth' controlHeaderParens' false braceDepth' controlBlockBraces' pendingControlBlock' (tok :: acc)

/-- Tokenize the full source string -/
def tokenize (source : String) : Except String (List Token) :=
  tokenizeChars source.toList 1 1 0 true 0 [] false 0 [] false []

end VerifiedJS.Source
