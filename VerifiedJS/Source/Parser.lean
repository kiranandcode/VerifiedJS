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

/-- Parser monad type alias (reserved for the full parser implementation). -/
abbrev Parser (α : Type) := ParserState → Except String (α × ParserState)

private def parseKeywordLiteral (s : String) : Option Expr :=
  match s with
  | "true" => some (.lit (.bool true))
  | "false" => some (.lit (.bool false))
  | "null" => some (.lit .null)
  | "undefined" => some (.lit .undefined)
  | _ => none

private def parseFromSingleToken (t : Token) : Except String Expr :=
  match t.kind with
  | .number n => pure (.lit (.number n))
  | .string s => pure (.lit (.string s))
  | .regex p f => pure (.lit (.regex p f))
  | .ident n => pure (.ident n)
  | .kw k =>
    match parseKeywordLiteral k with
    | some e => pure e
    | none => throw s!"Unsupported standalone keyword expression `{k}` at {t.pos.line}:{t.pos.col}"
  | _ => throw s!"Unsupported expression token at {t.pos.line}:{t.pos.col}"

private def tokensWithoutSeparators (tokens : List Token) : List Token :=
  tokens.filter (fun t =>
    match t.kind with
    | .newline => false
    | .punct ";" => false
    | _ => true)

/-- Parse a JavaScript source string into a Program AST.
    Baseline implementation: currently parses at most one simple expression statement. -/
def parse (source : String) : Except String Program := do
  let toks ← tokenize source
  let significant := tokensWithoutSeparators toks
  match significant with
  | [] => pure (.script [])
  | [t] =>
    match t.kind with
    | .eof => pure (.script [])
    | _ =>
      let e ← parseFromSingleToken t
      pure (.script [.expr e])
  | t :: _ =>
    match t.kind with
    | .eof => pure (.script [])
    | _ =>
      let e ← parseFromSingleToken t
      pure (.script [.expr e])

/-- Parse a single expression (useful for testing).
    Baseline implementation: parses the first non-separator token as an expression. -/
def parseExpr (source : String) : Except String Expr := do
  let toks ← tokenize source
  let significant := tokensWithoutSeparators toks
  match significant with
  | [] => throw "Empty input"
  | t :: _ =>
    match t.kind with
    | .eof => throw "Empty input"
    | _ => parseFromSingleToken t

end VerifiedJS.Source
