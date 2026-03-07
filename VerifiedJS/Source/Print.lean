/-
  VerifiedJS — AST Pretty Printer
  Round-trip: parse ∘ print ≈ id
-/

import VerifiedJS.Source.AST

namespace VerifiedJS.Source

/-- Pretty-print a Program back to JavaScript source. -/
def printProgram (_p : Program) : String :=
  "// VerifiedJS.Source.Print: TODO"

/-- Pretty-print a single expression. -/
def printExpr (_e : Expr) : String :=
  "/* expr */"

/-- Pretty-print a single statement. -/
def printStmt (_s : Stmt) : String :=
  "/* stmt */"

end VerifiedJS.Source
