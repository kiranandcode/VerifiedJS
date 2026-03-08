/-
  VerifiedJS — Lowering Correctness Proof
  JS.ANF → Wasm.IR semantic preservation.
-/

import VerifiedJS.Wasm.Lower

namespace VerifiedJS.Proofs

open VerifiedJS.Wasm

theorem runtimeIdx_getGlobal_fresh_from_arith :
    RuntimeIdx.getGlobal ≠ RuntimeIdx.binaryAdd ∧ RuntimeIdx.getGlobal ≠ RuntimeIdx.binaryNeq := by
  decide

theorem runtimeIdx_getGlobal_after_numeric_helpers :
    RuntimeIdx.binaryNeq < RuntimeIdx.getGlobal := by
  decide

-- TODO: State and prove lowering correctness theorem
-- theorem lower_correct (s : ANF.Program) (t : Wasm.IR.IRModule)
--     (h : Wasm.lower s = .ok t) :
--     <semantic preservation statement> := sorry

end VerifiedJS.Proofs
