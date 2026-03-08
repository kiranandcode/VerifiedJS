/-
  VerifiedJS — Wasm IR Reference Interpreter
  SPEC: WebAssembly Core 1.0 §4.4 (instruction execution), adapted for VerifiedJS IR.
-/

import VerifiedJS.Wasm.IR
import Std.Data.HashMap

namespace VerifiedJS.Wasm.IR

open Std

/-- Symbolic runtime value used by the IR reference interpreter. -/
abbrev Value := String

/-- Mutable interpreter state (stack/locals/globals/memory + textual trace). -/
structure ExecState where
  stack : List Value
  locals : Array Value
  globals : Array Value
  memories : Array (Std.HashMap Nat Value)
  trace : List String
  deriving Inhabited

/-- Control outcome of evaluating an instruction sequence. -/
inductive ExecSignal where
  | ok
  | branch (label : String)
  | ret
  | trap (msg : String)
  deriving Inhabited

private def defaultValue : IRType → Value
  | .i32 => "0"
  | .i64 => "0"
  | .f64 => "0.0"
  | .ptr => "null"

private def initialGlobals (m : IRModule) : Array Value :=
  m.globals.map (fun (_, _, init) => init)

private def initialMemories (m : IRModule) : Array (Std.HashMap Nat Value) :=
  Array.replicate m.memories.size {}

private def pushTrace (s : ExecState) (line : String) : ExecState :=
  { s with trace := s.trace ++ [line] }

private def trapState (s : ExecState) (msg : String) : ExecSignal × ExecState :=
  (.trap msg, pushTrace s s!"trap: {msg}")

private def pop1? (stack : List Value) : Option (Value × List Value) :=
  match stack with
  | v :: rest => some (v, rest)
  | [] => none

private def pop2? (stack : List Value) : Option (Value × Value × List Value) :=
  match stack with
  | v1 :: v2 :: rest => some (v1, v2, rest)
  | _ => none

private def popN? (n : Nat) (stack : List Value) : Option (List Value × List Value) := Id.run do
  let mut taken : List Value := []
  let mut rest := stack
  for _ in [0:n] do
    match rest with
    | v :: tail =>
        taken := v :: taken
        rest := tail
    | [] => return none
  return some (taken.reverse, rest)

private def parseNatLike? (s : String) : Option Nat :=
  let trimmed := s.trimAscii.toString
  if trimmed.startsWith "-" then
    none
  else
    trimmed.toNat?

private def asTruthy (v : Value) : Bool :=
  let t := v.trimAscii.toString
  !(t = "" || t = "0" || t = "0.0" || t = "false" || t = "null" || t = "undefined")

private def evalUnOp (op : String) (v : Value) : Value :=
  match op with
  | "eqz" => if asTruthy v then "0" else "1"
  | "neg" =>
      match parseNatLike? v with
      | some n => toString (0 - Int.ofNat n)
      | none => s!"neg({v})"
  | _ => s!"{op}({v})"

private def evalBinOp (op lhs rhs : String) : Value :=
  match parseNatLike? lhs, parseNatLike? rhs with
  | some a, some b =>
      match op with
      | "add" => toString (a + b)
      | "sub" => toString (a - b)
      | "mul" => toString (a * b)
      | "div" =>
          if b == 0 then "NaN" else toString (a / b)
      | "mod" =>
          if b == 0 then "NaN" else toString (a % b)
      | "eq" => if a == b then "1" else "0"
      | "neq" => if a == b then "0" else "1"
      | "lt" => if a < b then "1" else "0"
      | "gt" => if a > b then "1" else "0"
      | "le" => if a ≤ b then "1" else "0"
      | "ge" => if a ≥ b then "1" else "0"
      | _ => s!"({lhs} {op} {rhs})"
  | _, _ =>
      match op with
      | "strict_eq" => if lhs = rhs then "1" else "0"
      | "strict_neq" => if lhs = rhs then "0" else "1"
      | _ => s!"({lhs} {op} {rhs})"

mutual
private partial def runInstrs (m : IRModule) (code : List IRInstr) (fuel : Nat) (s : ExecState) :
    ExecSignal × ExecState × Nat :=
  match fuel with
  | 0 =>
      let (sig, s') := trapState s "interpreter fuel exhausted"
      (sig, s', 0)
  | f + 1 =>
      match code with
      | [] => (.ok, s, f + 1)
      | instr :: rest =>
          let (sig, s', f') := runInstr m instr (f + 1) s
          match sig with
          | .ok => runInstrs m rest f' s'
          | _ => (sig, s', f')

private partial def runLoop (m : IRModule) (label : String) (body : List IRInstr) (fuel : Nat)
    (s : ExecState) : ExecSignal × ExecState × Nat :=
  match fuel with
  | 0 =>
      let (sig, s') := trapState s s!"fuel exhausted in loop '{label}'"
      (sig, s', 0)
  | f + 1 =>
      let (sig, s', f') := runInstrs m body (f + 1) s
      match sig with
      | .ok => (.ok, s', f')
      | .ret => (.ret, s', f')
      | .trap msg => (.trap msg, s', f')
      | .branch target =>
          if target = label then
            runLoop m label body f' s'
          else
            (.branch target, s', f')

private partial def runCall (m : IRModule) (funcIdx : Nat) (fuel : Nat) (s : ExecState) :
    ExecSignal × ExecState × Nat :=
  match m.functions[funcIdx]? with
  | none => trapState s s!"unknown function index {funcIdx}" |> fun (sig, s') => (sig, s', fuel)
  | some fn =>
      match popN? fn.params.length s.stack with
      | none =>
          let (sig, s') := trapState s s!"stack underflow for call {funcIdx}"
          (sig, s', fuel)
      | some (args, callerStack) =>
          let localDefaults := fn.locals.map defaultValue
          let calleeLocals := (args ++ localDefaults).toArray
          let calleeState : ExecState :=
            { stack := []
              locals := calleeLocals
              globals := s.globals
              memories := s.memories
              trace := pushTrace s s!"call {fn.name}#{funcIdx}" |>.trace }
          let (sig, calleeOut, fuel') := runInstrs m fn.body fuel calleeState
          let mergeBack (stack : List Value) : ExecState :=
            { s with
              stack := stack
              globals := calleeOut.globals
              memories := calleeOut.memories
              trace := calleeOut.trace }
          match sig with
          | .trap msg => (.trap msg, mergeBack callerStack, fuel')
          | .branch target =>
              let (trapSig, trapSt) := trapState (mergeBack callerStack) s!"invalid escaping branch '{target}'"
              (trapSig, trapSt, fuel')
          | .ok | .ret =>
              match popN? fn.results.length calleeOut.stack with
              | none =>
                  let (trapSig, trapSt) := trapState (mergeBack callerStack) s!"missing results in call {funcIdx}"
                  (trapSig, trapSt, fuel')
              | some (results, _) =>
                  let outStack := results.reverse ++ callerStack
                  (.ok, mergeBack outStack, fuel')

private partial def runInstr (m : IRModule) (instr : IRInstr) (fuel : Nat) (s : ExecState) :
    ExecSignal × ExecState × Nat :=
  match fuel with
  | 0 =>
      let (sig, s') := trapState s "interpreter fuel exhausted"
      (sig, s', 0)
  | f + 1 =>
      match instr with
      | .const_ _ v => (.ok, { s with stack := v :: s.stack }, f)
      | .localGet idx =>
          match s.locals[idx]? with
          | some v => (.ok, { s with stack := v :: s.stack }, f)
          | none =>
              let (sig, s') := trapState s s!"local.get out of bounds: {idx}"
              (sig, s', f)
      | .localSet idx =>
          match pop1? s.stack with
          | some (v, rest) =>
              if idx < s.locals.size then
                (.ok, { s with locals := s.locals.set! idx v, stack := rest }, f)
              else
                let (sig, s') := trapState s s!"local.set out of bounds: {idx}"
                (sig, s', f)
          | none =>
              let (sig, s') := trapState s "stack underflow in local.set"
              (sig, s', f)
      | .globalGet idx =>
          match s.globals[idx]? with
          | some v => (.ok, { s with stack := v :: s.stack }, f)
          | none =>
              let (sig, s') := trapState s s!"global.get out of bounds: {idx}"
              (sig, s', f)
      | .globalSet idx =>
          match pop1? s.stack with
          | some (v, rest) =>
              if idx < s.globals.size then
                (.ok, { s with globals := s.globals.set! idx v, stack := rest }, f)
              else
                let (sig, s') := trapState s s!"global.set out of bounds: {idx}"
                (sig, s', f)
          | none =>
              let (sig, s') := trapState s "stack underflow in global.set"
              (sig, s', f)
      | .load _ offset =>
          match pop1? s.stack with
          | some (addrV, rest) =>
              match parseNatLike? addrV, s.memories[0]? with
              | some addr, some mem =>
                  let key := addr + offset
                  let out := (mem.get? key).getD "0"
                  (.ok, { s with stack := out :: rest }, f)
              | _, none =>
                  let (sig, s') := trapState s "no memory segment at index 0"
                  (sig, s', f)
              | none, _ =>
                  let (sig, s') := trapState s s!"invalid load address: {addrV}"
                  (sig, s', f)
          | none =>
              let (sig, s') := trapState s "stack underflow in load"
              (sig, s', f)
      | .store _ offset =>
          match pop2? s.stack with
          | some (value, addrV, rest) =>
              match parseNatLike? addrV, s.memories[0]? with
              | some addr, some mem =>
                  let mem' := mem.insert (addr + offset) value
                  let memories' := s.memories.set! 0 mem'
                  (.ok, { s with stack := rest, memories := memories' }, f)
              | _, none =>
                  let (sig, s') := trapState s "no memory segment at index 0"
                  (sig, s', f)
              | none, _ =>
                  let (sig, s') := trapState s s!"invalid store address: {addrV}"
                  (sig, s', f)
          | none =>
              let (sig, s') := trapState s "stack underflow in store"
              (sig, s', f)
      | .binOp _ op =>
          match pop2? s.stack with
          | some (rhs, lhs, rest) =>
              let out := evalBinOp op lhs rhs
              (.ok, { s with stack := out :: rest }, f)
          | none =>
              let (sig, s') := trapState s s!"stack underflow in binOp '{op}'"
              (sig, s', f)
      | .unOp _ op =>
          match pop1? s.stack with
          | some (v, rest) =>
              (.ok, { s with stack := evalUnOp op v :: rest }, f)
          | none =>
              let (sig, s') := trapState s s!"stack underflow in unOp '{op}'"
              (sig, s', f)
      | .call funcIdx => runCall m funcIdx f s
      | .callIndirect typeIdx =>
          -- Reference interpreter fallback: use `typeIdx` as a direct callee index.
          runCall m typeIdx f s
      | .block label body =>
          let (sig, s', f') := runInstrs m body f s
          match sig with
          | .branch target =>
              if target = label then
                (.ok, s', f')
              else
                (.branch target, s', f')
          | _ => (sig, s', f')
      | .loop label body => runLoop m label body f s
      | .if_ then_ else_ =>
          match pop1? s.stack with
          | some (cond, rest) =>
              let branch := if asTruthy cond then then_ else else_
              runInstrs m branch f { s with stack := rest }
          | none =>
              let (sig, s') := trapState s "stack underflow in if"
              (sig, s', f)
      | .br label => (.branch label, s, f)
      | .brIf label =>
          match pop1? s.stack with
          | some (cond, rest) =>
              if asTruthy cond then
                (.branch label, { s with stack := rest }, f)
              else
                (.ok, { s with stack := rest }, f)
          | none =>
              let (sig, s') := trapState s "stack underflow in br_if"
              (sig, s', f)
      | .return_ => (.ret, s, f)
      | .drop =>
          match pop1? s.stack with
          | some (_, rest) => (.ok, { s with stack := rest }, f)
          | none =>
              let (sig, s') := trapState s "stack underflow in drop"
              (sig, s', f)
      | .memoryGrow =>
          let oldSize := s.memories.size
          let grown := s.memories.push {}
          (.ok, { s with stack := toString oldSize :: s.stack, memories := grown }, f)
end

private def entryFunction? (m : IRModule) : Option Nat :=
  match m.startFunc with
  | some idx => some idx
  | none =>
      if 0 < m.functions.size then
        some 0
      else
        none

/-- Execute a Wasm.IR module from start function (or function 0 fallback) with bounded fuel. -/
def interp (m : IRModule) (fuel : Nat := 1000000) : IO Unit := do
  let initState : ExecState :=
    { stack := []
      locals := #[]
      globals := initialGlobals m
      memories := initialMemories m
      trace := [] }
  match entryFunction? m with
  | none =>
      IO.println "Wasm.IR interp: module has no functions"
  | some idx =>
      let (sig, finalState, _) := runCall m idx fuel initState
      match sig with
      | .ok =>
          IO.println s!"Wasm.IR interp: completed, stack={finalState.stack.reverse}"
      | .ret =>
          IO.println s!"Wasm.IR interp: return, stack={finalState.stack.reverse}"
      | .branch lbl =>
          IO.println s!"Wasm.IR interp: invalid escaped branch '{lbl}'"
      | .trap msg =>
          IO.println s!"Wasm.IR interp: trap: {msg}"

end VerifiedJS.Wasm.IR
