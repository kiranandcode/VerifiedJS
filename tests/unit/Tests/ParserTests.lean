import VerifiedJS.Source.Parser

namespace Tests

open VerifiedJS.Source

def isDivThenNumber (toks : List Token) : Bool :=
  match toks with
  | [ { kind := .ident "a", .. }
    , { kind := .punct "/", .. }
    , { kind := .number _, .. }
    , { kind := .eof, .. }
    ] => true
  | _ => false

def hasRegexLiteral (toks : List Token) : Bool :=
  match toks with
  | [ { kind := .kw "return", .. }
    , { kind := .regex "ab+" "gi", .. }
    , { kind := .eof, .. }
    ] => true
  | _ => false

def commentIsIgnored (toks : List Token) : Bool :=
  match toks with
  | [ { kind := .ident "a", .. }
    , { kind := .punct "/", .. }
    , { kind := .ident "b", .. }
    , { kind := .eof, .. }
    ] => true
  | _ => false

def slashAfterIfHeaderIsRegex (toks : List Token) : Bool :=
  match toks with
  | [ { kind := .kw "if", .. }
    , { kind := .punct "(", .. }
    , { kind := .ident "x", .. }
    , { kind := .punct ")", .. }
    , { kind := .regex "ab+" "", .. }
    , { kind := .punct ".", .. }
    , { kind := .ident "test", .. }
    , { kind := .punct "(", .. }
    , { kind := .ident "y", .. }
    , { kind := .punct ")", .. }
    , { kind := .eof, .. }
    ] => true
  | _ => false

def regexCharClassKeepsSlash (toks : List Token) : Bool :=
  match toks with
  | [ { kind := .kw "return", .. }
    , { kind := .regex "[a/b]+" "g", .. }
    , { kind := .eof, .. }
    ] => true
  | _ => false

def isMulPrecedence : Expr -> Bool
  | .binary .add (.lit (.number _)) (.binary .mul (.lit (.number _)) (.lit (.number _))) => true
  | _ => false

def isAssignAdd : Expr -> Bool
  | .assign .assign (.ident "a") (.binary .add (.ident "b") (.ident "c")) => true
  | _ => false

def isMemberCallIndex : Expr -> Bool
  | .index (.call (.member (.ident "obj") "prop") [.lit (.number _), .ident "x"]) (.ident "y") => true
  | _ => false

def isParenArrowExpr : Expr -> Bool
  | .arrowFunction [.ident "a" none, .ident "b" none] (.expr (.binary .add (.ident "a") (.ident "b"))) => true
  | _ => false

def isLetConstReturn : Program -> Bool
  | .script
      [ .varDecl .let_ [.mk (.ident "x" none) (some (.binary .add (.lit (.number _)) (.lit (.number _))))]
      , .varDecl .const_ [.mk (.ident "y" none) (some (.ident "x"))]
      , .return (some (.ident "y"))
      ] => true
  | _ => false

def isBlockWithAssign : Program -> Bool
  | .script
      [ .block
        [ .varDecl .let_ [.mk (.ident "x" none) (some (.lit (.number _)))]
        , .expr (.assign .assign (.ident "x") (.binary .add (.ident "x") (.lit (.number _))))
        ]
      ] => true
  | _ => false

def isIfElseStmt : Program -> Bool
  | .script
      [ .if (.binary .lt (.ident "x") (.lit (.number _)))
          (.block [.return (some (.ident "x"))])
          (some (.block [.return (some (.lit (.number _)))]))
      ] => true
  | _ => false

def isForStmt : Program -> Bool
  | .script
      [ .for (some (.varDecl .let_ [.mk (.ident "i" none) (some (.lit (.number _)))]))
          (some (.binary .lt (.ident "i") (.lit (.number _))))
          (some (.assign .assign (.ident "i") (.binary .add (.ident "i") (.lit (.number _)))))
          (.block [.expr (.call (.member (.ident "console") "log") [.ident "i"])])
      ] => true
  | _ => false

def isFunctionDecl : Program -> Bool
  | .script
      [ .functionDecl "inc" [.ident "x" none]
          [ .return (some (.binary .add (.ident "x") (.lit (.number _)))) ]
          false false
      ] => true
  | _ => false

def isImportDefaultNamed : Program -> Bool
  | .script
      [ .import_
          [ .default_ "mainDefault"
          , .named "foo" "foo"
          , .named "bar" "baz"
          ]
          "pkg"
      ] => true
  | _ => false

def isDynamicImportExpr : Expr -> Bool
  | .importCall (.lit (.string "pkg")) [] => true
  | _ => false

def isImportMetaExpr : Expr -> Bool
  | .importMeta => true
  | _ => false

def isNewTargetExpr : Expr -> Bool
  | .newTarget => true
  | _ => false

def isSuperMemberCall : Expr -> Bool
  | .call (.member .super "m") [.ident "x"] => true
  | _ => false

def isDynamicImportStmt : Program -> Bool
  | .script [ .expr (.importCall (.lit (.string "pkg")) []) ] => true
  | _ => false

#guard
  match parseExpr "1 + 2 * 3" with
  | .ok e => isMulPrecedence e
  | .error _ => false

#guard
  match parseExpr "a = b + c" with
  | .ok e => isAssignAdd e
  | .error _ => false

#guard
  match parseExpr "obj.prop(1, x)[y]" with
  | .ok e => isMemberCallIndex e
  | .error _ => false

#guard
  match parseExpr "(a, b) => a + b" with
  | .ok e => isParenArrowExpr e
  | .error _ => false

#guard
  match parse "let x = 1 + 2; const y = x; return y" with
  | .ok p => isLetConstReturn p
  | .error _ => false

#guard
  match parse "{ let x = 1; x = x + 1; }" with
  | .ok p => isBlockWithAssign p
  | .error _ => false

#guard
  match parse "if (x < 1) { return x; } else { return 0; }" with
  | .ok p => isIfElseStmt p
  | .error _ => false

#guard
  match parse "for (let i = 0; i < 3; i = i + 1) { console.log(i); }" with
  | .ok p => isForStmt p
  | .error _ => false

#guard
  match parse "function inc(x) { return x + 1; }" with
  | .ok p => isFunctionDecl p
  | .error _ => false

#guard
  match parse "import mainDefault, { foo, bar as baz } from \"pkg\";" with
  | .ok p => isImportDefaultNamed p
  | .error _ => false

#guard
  match parseExpr "import(\"pkg\")" with
  | .ok e => isDynamicImportExpr e
  | .error _ => false

#guard
  match parseExpr "import.meta" with
  | .ok e => isImportMetaExpr e
  | .error _ => false

#guard
  match parseExpr "new.target" with
  | .ok e => isNewTargetExpr e
  | .error _ => false

#guard
  match parseExpr "super.m(x)" with
  | .ok e => isSuperMemberCall e
  | .error _ => false

#guard
  match parse "import(\"pkg\");" with
  | .ok p => isDynamicImportStmt p
  | .error _ => false

#guard
  match tokenize "a / 2" with
  | .ok toks => isDivThenNumber toks
  | .error _ => false

#guard
  match tokenize "return /ab+/gi" with
  | .ok toks => hasRegexLiteral toks
  | .error _ => false

#guard
  match tokenize "a/*x*/ / b // trailing comment" with
  | .ok toks => commentIsIgnored toks
  | .error _ => false

#guard
  match tokenize "if (x) /ab+/.test(y)" with
  | .ok toks => slashAfterIfHeaderIsRegex toks
  | .error _ => false

#guard
  match tokenize "return /[a/b]+/g" with
  | .ok toks => regexCharClassKeepsSlash toks
  | .error _ => false

end Tests
