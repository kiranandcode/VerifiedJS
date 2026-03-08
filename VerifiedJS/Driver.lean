/-
  VerifiedJS — CLI Driver
  Main entry point for the compiler.
-/

import VerifiedJS.Source.Parser
import VerifiedJS.Source.AST
import VerifiedJS.Core.Elaborate
import VerifiedJS.Core.Print
import VerifiedJS.Core.Interp
import VerifiedJS.Flat.ClosureConvert
import VerifiedJS.Flat.Print
import VerifiedJS.Flat.Interp
import VerifiedJS.ANF.Convert
import VerifiedJS.ANF.Optimize
import VerifiedJS.ANF.Print
import VerifiedJS.ANF.Interp
import VerifiedJS.Wasm.Lower
import VerifiedJS.Wasm.Emit
import VerifiedJS.Wasm.Print
import VerifiedJS.Wasm.Binary
import VerifiedJS.Wasm.IR
import VerifiedJS.Wasm.IRPrint
import VerifiedJS.Wasm.IRInterp
import VerifiedJS.Util

open VerifiedJS

/-- Association-list lookup by key. -/
private def lookupKey? {α : Type} (xs : List (String × α)) (k : String) : Option α :=
  match xs with
  | [] => none
  | (k', v) :: rest => if k = k' then some v else lookupKey? rest k

/-- Association-list insert/update by key. -/
private def upsertKey {α : Type} (xs : List (String × α)) (k : String) (v : α) : List (String × α) :=
  match xs with
  | [] => [(k, v)]
  | (k', v') :: rest =>
    if k = k' then
      (k, v) :: rest
    else
      (k', v') :: upsertKey rest k v

/-- Concatenate parent directory and import source. -/
private def resolveImportPath (currentFile importSource : String) : IO (Except String String) := do
  if !(importSource.startsWith ".") then
    return .error s!"Unsupported module specifier (only relative imports supported): {importSource}"
  let baseDir := (System.FilePath.mk currentFile).parent.getD "."
  let candidate := (baseDir / importSource)
  if (← candidate.pathExists) then
    return .ok (toString (← IO.FS.realPath candidate))
  let withJs := candidate.withExtension "js"
  if (← withJs.pathExists) then
    return .ok (toString (← IO.FS.realPath withJs))
  let indexJs := candidate / "index.js"
  if (← indexJs.pathExists) then
    return .ok (toString (← IO.FS.realPath indexJs))
  return .error s!"Cannot resolve import `{importSource}` from `{currentFile}`"

/-- Extract plain statements from a parsed Source program. -/
private def programToStmts (p : Source.Program) : List Source.Stmt :=
  match p with
  | .script stmts => stmts
  | .module_ stmts => stmts
  | .scriptItems items =>
    items.foldr (fun item acc =>
      match item with
      | .directive _ => acc
      | .stmt s => s :: acc) []
  | .moduleItems items =>
    items.foldr (fun item acc =>
      match item with
      | .stmt s => s :: acc
      | .importDecl d =>
        match d with
        | .sideEffect src _ => (.import_ [] src) :: acc
        | .withClause specs src _ => (.import_ specs src) :: acc
      | .exportDecl d =>
        match d with
        | .named specs src => (.export_ (.named specs src)) :: acc
        | .defaultExpr e => (.export_ (.default_ e)) :: acc
        | .defaultFunction name params body _ _ =>
          let fnExpr : Source.Expr := .function name params body
          (.export_ (.default_ fnExpr)) :: acc
        | .defaultClass name superClass body =>
          let clsExpr : Source.Expr := .«class» name superClass body
          (.export_ (.default_ clsExpr)) :: acc
        | .declaration decl => (.export_ (.decl decl)) :: acc
        | .allFrom src alias_ => (.export_ (.all src alias_)) :: acc
      ) []

/-- Import edges directly required by a module file. -/
private def moduleImportEdges (stmts : List Source.Stmt) : List String :=
  stmts.foldr (fun s acc =>
    match s with
    | .import_ _ src => src :: acc
    | .export_ (.named _ (some src)) => src :: acc
    | .export_ (.all src _) => src :: acc
    | _ => acc) []

/-- Bound names in a binding pattern. -/
private partial def patternBoundNames (p : Source.Pattern) : List String :=
  match p with
  | .ident n _ => [n]
  | .array elems rest =>
    let elemNames := elems.foldr (fun e acc =>
      match e with
      | some p' => patternBoundNames p' ++ acc
      | none => acc) []
    let restNames := match rest with | some r => patternBoundNames r | none => []
    elemNames ++ restNames
  | .object props rest =>
    let propNames := props.foldr (fun prop acc =>
      match prop with
      | .keyValue _ v => patternBoundNames v ++ acc
      | .shorthand n _ => n :: acc) []
    let restNames := match rest with | some r => patternBoundNames r | none => []
    propNames ++ restNames
  | .assign pat _ => patternBoundNames pat

/-- Names declared by a statement at its own level. -/
private def stmtDeclaredNames (s : Source.Stmt) : List String :=
  match s with
  | .varDecl _ decls =>
    decls.foldr (fun d acc =>
      match d with
      | .mk pat _ => patternBoundNames pat ++ acc) []
  | .functionDecl name _ _ _ _ => [name]
  | .classDecl name _ _ => [name]
  | .export_ (.decl st) => stmtDeclaredNames st
  | _ => []

/-- Rename map from local name to canonical imported/exported binding. -/
abbrev RenameMap := List (String × String)
/-- Namespace import map: local namespace name to exported-name table. -/
abbrev NamespaceMap := List (String × List (String × String))

private def renameLookup (m : RenameMap) (name : String) : Option String := lookupKey? m name
private def nsLookup (m : NamespaceMap) (name : String) : Option (List (String × String)) := lookupKey? m name

/-- Rename declaration patterns for canonical exported bindings. -/
private partial def rewriteDeclPattern (ren : RenameMap) (p : Source.Pattern) : Source.Pattern :=
  match p with
  | .ident n init =>
    let n' := (renameLookup ren n).getD n
    .ident n' init
  | .array elems rest =>
    .array (elems.map (Option.map (rewriteDeclPattern ren))) (rest.map (rewriteDeclPattern ren))
  | .object props rest =>
    .object (props.map (fun prop =>
      match prop with
      | .keyValue k v => .keyValue k (rewriteDeclPattern ren v)
      | .shorthand n init =>
        let n' := (renameLookup ren n).getD n
        .shorthand n' init
    )) (rest.map (rewriteDeclPattern ren))
  | .assign pat init => .assign (rewriteDeclPattern ren pat) init

/-- Enumerate list values with Nat indices. -/
private def enumerate {α : Type} (xs : List α) : List (Nat × α) :=
  let rec go (i : Nat) (ys : List α) : List (Nat × α) :=
    match ys with
    | [] => []
    | y :: rest => (i, y) :: go (i + 1) rest
  go 0 xs

/-- Rewrite expression references according to module binding maps. -/
private partial def rewriteExpr (ren : RenameMap) (ns : NamespaceMap) (e : Source.Expr) : Source.Expr :=
  match e with
  | .ident n =>
    match renameLookup ren n with
    | some n' => .ident n'
    | none => e
  | .member (.ident nsName) prop =>
    match nsLookup ns nsName with
    | some table =>
      match lookupKey? table prop with
      | some n' => .ident n'
      | none => .member (.ident nsName) prop
    | none => .member (.ident nsName) prop
  | .index (.ident nsName) (.lit (.string prop)) =>
    match nsLookup ns nsName with
    | some table =>
      match lookupKey? table prop with
      | some n' => .ident n'
      | none => .index (.ident nsName) (.lit (.string prop))
    | none => .index (.ident nsName) (.lit (.string prop))
  | .array elems => .array (elems.map (Option.map (rewriteExpr ren ns)))
  | .object props =>
    .object (props.map (fun p =>
      match p with
      | .keyValue k v => .keyValue k (rewriteExpr ren ns v)
      | .shorthand n =>
        match renameLookup ren n with
        | some n' => .keyValue (.ident n) (.ident n')
        | none => p
      | .method kind k ps body isAsync isGenerator =>
        .method kind k ps body isAsync isGenerator
      | .spread ex => .spread (rewriteExpr ren ns ex)))
  | .unary op arg => .unary op (rewriteExpr ren ns arg)
  | .binary op lhs rhs => .binary op (rewriteExpr ren ns lhs) (rewriteExpr ren ns rhs)
  | .assign op lhs rhs => .assign op lhs (rewriteExpr ren ns rhs)
  | .conditional c t el => .conditional (rewriteExpr ren ns c) (rewriteExpr ren ns t) (rewriteExpr ren ns el)
  | .call c args => .call (rewriteExpr ren ns c) (args.map (rewriteExpr ren ns))
  | .«new» c args => .«new» (rewriteExpr ren ns c) (args.map (rewriteExpr ren ns))
  | .member obj prop => .member (rewriteExpr ren ns obj) prop
  | .index obj prop => .index (rewriteExpr ren ns obj) (rewriteExpr ren ns prop)
  | .privateMember obj pn => .privateMember (rewriteExpr ren ns obj) pn
  | .optionalChain ex chain => .optionalChain (rewriteExpr ren ns ex) chain
  | .template tag parts => .template (tag.map (rewriteExpr ren ns)) parts
  | .spread ex => .spread (rewriteExpr ren ns ex)
  | .yield arg delegate => .yield (arg.map (rewriteExpr ren ns)) delegate
  | .await arg => .await (rewriteExpr ren ns arg)
  | .sequence xs => .sequence (xs.map (rewriteExpr ren ns))
  | .importCall src attrs => .importCall (rewriteExpr ren ns src) attrs
  | .privateIn p rhs => .privateIn p (rewriteExpr ren ns rhs)
  | _ => e

/-- Rewrite statement references according to module binding maps. -/
private partial def rewriteStmt (ren : RenameMap) (ns : NamespaceMap) (s : Source.Stmt) : Source.Stmt :=
  match s with
  | .expr e => .expr (rewriteExpr ren ns e)
  | .block stmts => .block (stmts.map (rewriteStmt ren ns))
  | .varDecl k decls =>
    .varDecl k (decls.map (fun d =>
      match d with
      | .mk p init => .mk (rewriteDeclPattern ren p) (init.map (rewriteExpr ren ns))))
  | .«if» c t el => .«if» (rewriteExpr ren ns c) (rewriteStmt ren ns t) (el.map (rewriteStmt ren ns))
  | .while_ c b => .while_ (rewriteExpr ren ns c) (rewriteStmt ren ns b)
  | .doWhile b c => .doWhile (rewriteStmt ren ns b) (rewriteExpr ren ns c)
  | .«for» init c u b =>
    let init' := init.map (fun i =>
      match i with
      | .varDecl k ds => .varDecl k (ds.map (fun d =>
          match d with
          | .mk p v => .mk (rewriteDeclPattern ren p) (v.map (rewriteExpr ren ns))))
      | .expr e => .expr (rewriteExpr ren ns e))
    .«for» init' (c.map (rewriteExpr ren ns)) (u.map (rewriteExpr ren ns)) (rewriteStmt ren ns b)
  | .forIn k lhs rhs body => .forIn k lhs (rewriteExpr ren ns rhs) (rewriteStmt ren ns body)
  | .forOf k lhs rhs body => .forOf k lhs (rewriteExpr ren ns rhs) (rewriteStmt ren ns body)
  | .forOfEx k lhs rhs body mode => .forOfEx k lhs (rewriteExpr ren ns rhs) (rewriteStmt ren ns body) mode
  | .«switch» disc cases =>
    .«switch» (rewriteExpr ren ns disc) (cases.map (fun c =>
      match c with
      | .case_ test body => .case_ (rewriteExpr ren ns test) (body.map (rewriteStmt ren ns))
      | .default_ body => .default_ (body.map (rewriteStmt ren ns))))
  | .«try» body catch_ finally_ =>
    .«try» (body.map (rewriteStmt ren ns))
      (catch_.map (fun c =>
        match c with
        | .mk p b => .mk p (b.map (rewriteStmt ren ns))))
      (finally_.map (List.map (rewriteStmt ren ns)))
  | .throw arg => .throw (rewriteExpr ren ns arg)
  | .«return» arg => .«return» (arg.map (rewriteExpr ren ns))
  | .labeled l b => .labeled l (rewriteStmt ren ns b)
  | .with o b => .with (rewriteExpr ren ns o) (rewriteStmt ren ns b)
  | .functionDecl n ps body isAsync isGenerator =>
    .functionDecl ((renameLookup ren n).getD n) ps (body.map (rewriteStmt ren ns)) isAsync isGenerator
  | .classDecl n sup body =>
    .classDecl ((renameLookup ren n).getD n) (sup.map (rewriteExpr ren ns)) body
  | .import_ _ _ => s
  | .export_ _ => s
  | _ => s

/-- Create `var <name> = <expr>` declaration statement. -/
private def mkVarAssignStmt (name : String) (expr : Source.Expr) : Source.Stmt :=
  .varDecl .var [Source.VarDeclarator.mk (.ident name none) (some expr)]

/-- Parse source file and return top-level statements. -/
private def parseFileToStmts (path : String) : IO (Except String (List Source.Stmt)) := do
  let source ← IO.FS.readFile ⟨path⟩
  match Source.parse source with
  | .ok prog => return .ok (programToStmts prog)
  | .error e => return .error s!"Parse error in `{path}`: {e}"

/-- Load a module graph in dependency order (deps first). -/
private partial def loadModuleGraph
    (path : String)
    (stack : List String)
    (seen : List String)
    (mods : List (String × List Source.Stmt))
    : IO (Except String (List String × List (String × List Source.Stmt))) := do
  if stack.contains path then
    return .error s!"Cyclic module import detected at `{path}`"
  if seen.contains path then
    return .ok (seen, mods)
  let parsed ← parseFileToStmts path
  match parsed with
  | .error e => return .error e
  | .ok stmts =>
    let imports := moduleImportEdges stmts
    let mut seenCur := seen
    let mut modsCur := mods
    for src in imports do
      let resolved ← resolveImportPath path src
      match resolved with
      | .error e => return .error e
      | .ok dep =>
        let loaded ← loadModuleGraph dep (path :: stack) seenCur modsCur
        match loaded with
        | .error e => return .error e
        | .ok (seenNext, modsNext) =>
          seenCur := seenNext
          modsCur := modsNext
    let seen' := path :: seenCur
    let mods' := (path, stmts) :: modsCur
    return .ok (seen', mods')

/-- Build a linked single script from an entry module and its transitive deps. -/
private def linkEntryModule (entryFile : String) : IO (Except String Source.Program) := do
  let entryReal := toString (← IO.FS.realPath ⟨entryFile⟩)
  let loaded ← loadModuleGraph entryReal [] [] []
  match loaded with
  | .error e => return .error e
  | .ok (_, modulesRev) =>
    let modules := modulesRev.reverse
    let moduleIds : List (String × Nat) :=
      (enumerate modules).map (fun (i, p) => (p.fst, i))
    let canon (path : String) (name : String) : String :=
      let id := (lookupKey? moduleIds path).getD 0
      s!"__m{id}_{name}"
    let mut linked : List Source.Stmt := []
    let mut exportsByModule : List (String × List (String × String)) := []

    for (path, stmts) in modules do
      let mut renames : RenameMap := []
      let mut namespaces : NamespaceMap := []
      let mut moduleOut : List Source.Stmt := []
      let mut moduleExports : List (String × String) := []

      -- Resolve imports into binding rewrites.
      for s in stmts do
        match s with
        | .import_ specs src => do
          let resolved ← resolveImportPath path src
          match resolved with
          | .error e => return .error e
          | .ok depPath =>
            let depExports := (lookupKey? exportsByModule depPath).getD []
            for sp in specs do
              match sp with
              | .default_ localName =>
                match lookupKey? depExports "default" with
                | some rhs => renames := upsertKey renames localName rhs
                | none => return .error s!"Missing default export in `{depPath}` imported by `{path}`"
              | .named imported localName =>
                match lookupKey? depExports imported with
                | some rhs => renames := upsertKey renames localName rhs
                | none => return .error s!"Missing export `{imported}` in `{depPath}` imported by `{path}`"
              | .namespace localName =>
                namespaces := upsertKey namespaces localName depExports
                -- Namespace object fallback (snapshot; property accesses still rewritten live).
                let props : List Source.Property :=
                  depExports.map (fun (exportName, rhsName) => .keyValue (.ident exportName) (.ident rhsName))
                moduleOut := moduleOut ++ [mkVarAssignStmt localName (.object props)]
        | _ => pure ()

      -- Pre-seed local export bindings so exported locals become canonical vars.
      for s in stmts do
        match s with
        | .export_ (.decl declStmt) =>
          for n in stmtDeclaredNames declStmt do
            let rhs := canon path n
            renames := upsertKey renames n rhs
            moduleExports := upsertKey moduleExports n rhs
        | .export_ (.named specs none) =>
          for spec in specs do
            match spec with
            | .mk localName exportedName =>
              let rhs := (renameLookup renames localName).getD localName
              moduleExports := upsertKey moduleExports exportedName rhs
        | _ => pure ()

      -- Emit module body + export bindings/re-exports.
      for s in stmts do
        match s with
        | .import_ _ _ => pure ()
        | .export_ decl =>
          match decl with
          | .decl declStmt =>
            moduleOut := moduleOut ++ [rewriteStmt renames namespaces declStmt]
          | .default_ ex =>
            let rhs := canon path "default"
            moduleExports := upsertKey moduleExports "default" rhs
            moduleOut := moduleOut ++ [mkVarAssignStmt rhs (rewriteExpr renames namespaces ex)]
          | .named specs none =>
            for spec in specs do
              match spec with
              | .mk localName exportedName =>
                let rhs := (renameLookup renames localName).getD localName
                moduleExports := upsertKey moduleExports exportedName rhs
          | .named specs (some src) =>
            let resolved ← resolveImportPath path src
            match resolved with
            | .error e => return .error e
            | .ok depPath =>
              let depExports := (lookupKey? exportsByModule depPath).getD []
              for spec in specs do
                match spec with
                | .mk imported exportedName =>
                  match lookupKey? depExports imported with
                  | some rhs => moduleExports := upsertKey moduleExports exportedName rhs
                  | none =>
                    return .error s!"Missing re-export `{imported}` in `{depPath}` for `{path}`"
          | .all src alias_ =>
            let resolved ← resolveImportPath path src
            match resolved with
            | .error e => return .error e
            | .ok depPath =>
              let depExports := (lookupKey? exportsByModule depPath).getD []
              match alias_ with
              | some name =>
                let props : List Source.Property :=
                  depExports.filter (fun kv => kv.fst ≠ "default")
                    |>.map (fun (exportName, rhsName) => .keyValue (.ident exportName) (.ident rhsName))
                let nsVar := canon path ("ns_" ++ name)
                moduleOut := moduleOut ++ [mkVarAssignStmt nsVar (.object props)]
                moduleExports := upsertKey moduleExports name nsVar
              | none =>
                for (n, rhs) in depExports do
                  if n ≠ "default" then
                    moduleExports := upsertKey moduleExports n rhs
        | other =>
          moduleOut := moduleOut ++ [rewriteStmt renames namespaces other]

      exportsByModule := upsertKey exportsByModule path moduleExports
      linked := linked ++ moduleOut

    return .ok (.script linked)

/-- Helper: run pipeline through elaboration -/
private def elaborate (ast : Source.Program) : Except String Core.Program :=
  Core.elaborate ast

/-- Helper: run pipeline through closure conversion -/
private def toFlat (ast : Source.Program) : Except String Flat.Program := do
  let core ← elaborate ast
  Flat.closureConvert core

/-- Helper: run pipeline through ANF conversion + optimization -/
private def toANF (ast : Source.Program) : Except String ANF.Program := do
  let flat ← toFlat ast
  let anf ← ANF.convert flat
  pure (ANF.optimize anf)

/-- Helper: run pipeline through Wasm IR lowering -/
private def toWasmIR (ast : Source.Program) : Except String Wasm.IR.IRModule := do
  let anf ← toANF ast
  Wasm.lower anf

/-- Helper: run pipeline through Wasm AST emission -/
private def toWasm (ast : Source.Program) : Except String Wasm.Module := do
  let ir ← toWasmIR ast
  Wasm.emit ir

/-- Helper: print trace events from interpreters -/
private def printTrace (trace : List Core.TraceEvent) : IO Unit := do
  for event in trace do
    match event with
    | .log s => IO.println s
    | .error s => IO.eprintln s!"Error: {s}"
    | .silent => pure ()

/-- Emit targets for --emit flag -/
inductive EmitTarget where
  | core | flat | anf | wasmIR | wat
  deriving Repr, BEq

/-- Run targets for --run flag -/
inductive RunTarget where
  | core | flat | anf | wasmIR
  deriving Repr, BEq

def parseEmitTarget (s : String) : Option EmitTarget :=
  match s with
  | "core" => some .core
  | "flat" => some .flat
  | "anf" => some .anf
  | "wasmIR" => some .wasmIR
  | "wat" => some .wat
  | _ => none

def parseRunTarget (s : String) : Option RunTarget :=
  match s with
  | "core" => some .core
  | "flat" => some .flat
  | "anf" => some .anf
  | "wasmIR" => some .wasmIR
  | _ => none

def printUsage : IO Unit := do
  IO.println "Usage: verifiedjs <input.js> [options]"
  IO.println ""
  IO.println "Options:"
  IO.println "  -o <file>       Output .wasm file"
  IO.println "  --parse-only    Parse input and exit (no elaboration/lowering)"
  IO.println "  --module        Treat input as module entry and resolve imports/exports"
  IO.println "  --emit=<target> Print intermediate representation"
  IO.println "                  Targets: core, flat, anf, wasmIR, wat"
  IO.println "  --run=<target>  Interpret at a given IL level"
  IO.println "                  Targets: core, flat, anf, wasmIR"
  IO.println "  --help          Show this help"

def findOutputFile : List String → String
  | "-o" :: path :: _ => path
  | _ :: rest => findOutputFile rest
  | [] => "output.wasm"

def main (args : List String) : IO UInt32 := do
  if args.isEmpty || args.contains "--help" then
    printUsage
    return 0

  let inputFile := args.head!

  let moduleMode := args.contains "--module"

  -- Read and parse (or link) source
  let ast ←
    if moduleMode then
      let linked ← linkEntryModule inputFile
      match linked with
      | .ok p => pure p
      | .error e => do IO.eprintln s!"Module linking error: {e}"; return 1
    else
      let source ← IO.FS.readFile ⟨inputFile⟩
      match Source.parse source with
      | .ok ast => pure ast
      | .error e => do IO.eprintln s!"Parse error: {e}"; return 1

  if args.contains "--parse-only" then
    let _ := ast
    IO.println "Parse OK"
    return 0

  -- Check for --emit flag
  for arg in args do
    if arg.startsWith "--emit=" then
      let target := (arg.drop 7).toString
      match parseEmitTarget target with
      | some .core => do
        match elaborate ast with
        | .ok core => IO.println (Core.printProgram core)
        | .error e => IO.eprintln s!"Elaboration error: {e}"
      | some .flat => do
        match toFlat ast with
        | .ok flat => IO.println (Flat.printProgram flat)
        | .error e => IO.eprintln s!"Pipeline error: {e}"
      | some .anf => do
        match toANF ast with
        | .ok anf => IO.println (ANF.printProgram anf)
        | .error e => IO.eprintln s!"Pipeline error: {e}"
      | some .wasmIR => do
        match toWasmIR ast with
        | .ok ir => IO.println (Wasm.IR.printModule ir)
        | .error e => IO.eprintln s!"Pipeline error: {e}"
      | some .wat => do
        match toWasm ast with
        | .ok wasm => IO.println (Wasm.printWat wasm)
        | .error e => IO.eprintln s!"Pipeline error: {e}"
      | none => IO.eprintln s!"Unknown emit target: {target}"
      return 0

  -- Check for --run flag
  for arg in args do
    if arg.startsWith "--run=" then
      let target := (arg.drop 6).toString
      match parseRunTarget target with
      | some .core => do
        match elaborate ast with
        | .ok core => do
          let trace ← Core.interp core
          printTrace trace
        | .error e => IO.eprintln s!"Elaboration error: {e}"
      | some .flat => do
        match toFlat ast with
        | .ok flat => do
          let trace ← Flat.interp flat
          printTrace trace
        | .error e => IO.eprintln s!"Pipeline error: {e}"
      | some .anf => do
        match toANF ast with
        | .ok anf => do
          let trace ← ANF.interp anf
          printTrace trace
        | .error e => IO.eprintln s!"Pipeline error: {e}"
      | some .wasmIR => do
        match toWasmIR ast with
        | .ok ir => Wasm.IR.interp ir
        | .error e => IO.eprintln s!"Pipeline error: {e}"
      | none => IO.eprintln s!"Unknown run target: {target}"
      return 0

  -- Default: compile to wasm
  let outputFile := findOutputFile args

  match toWasm ast with
  | .ok wasm => do
    Wasm.writeWasm wasm outputFile
    IO.println s!"Compiled to {outputFile}"
    return 0
  | .error e => do
    IO.eprintln s!"Compilation error: {e}"
    return 1
