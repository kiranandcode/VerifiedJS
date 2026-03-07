/-
  VerifiedJS — CLI Driver
  Main entry point for the compiler.
-/

import VerifiedJS.Source.Parser
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

  -- Read source file
  let source ← IO.FS.readFile ⟨inputFile⟩

  -- Parse
  let ast ← match Source.parse source with
    | .ok ast => pure ast
    | .error e => do IO.eprintln s!"Parse error: {e}"; return 1

  -- Check for --emit flag
  for arg in args do
    if arg.startsWith "--emit=" then
      let target := (arg.drop 7).toString
      match parseEmitTarget target with
      | some .core => do
        match Core.elaborate ast with
        | .ok core => IO.println (Core.printProgram core)
        | .error e => IO.eprintln s!"Elaboration error: {e}"
      | some _ => IO.println s!"TODO: emit {target}"
      | none => IO.eprintln s!"Unknown emit target: {target}"
      return 0

  -- Check for --run flag
  for arg in args do
    if arg.startsWith "--run=" then
      let target := (arg.drop 6).toString
      match parseRunTarget target with
      | some .core => do
        match Core.elaborate ast with
        | .ok core => do
          let trace ← Core.interp core
          for event in trace do
            match event with
            | .log s => IO.println s
            | .error s => IO.eprintln s!"Error: {s}"
            | .silent => pure ()
        | .error e => IO.eprintln s!"Elaboration error: {e}"
      | some _ => IO.println s!"TODO: run {target}"
      | none => IO.eprintln s!"Unknown run target: {target}"
      return 0

  -- Default: compile to wasm
  -- Find output file
  let outputFile := findOutputFile args

  IO.println s!"TODO: Full compilation pipeline to {outputFile}"
  return 0
