/-
  VerifiedJS — Closure Conversion Correctness Proof
  JS.Core → JS.Flat semantic preservation.
-/

import VerifiedJS.Flat.ClosureConvert
import VerifiedJS.Core.Semantics
import VerifiedJS.Flat.Semantics

namespace VerifiedJS.Proofs

private theorem closureConvert_step_simulation
    (s : Core.Program) (t : Flat.Program)
    (h : Flat.closureConvert s = .ok t) :
    ∀ (sf sf' : Flat.State) (ev : Core.TraceEvent),
      Flat.Step sf ev sf' →
      ∃ (sc sc' : Core.State), Core.Step sc ev sc' := by
  intro sf sf' ev hstep
  -- Automation-first pipeline requested in README/user guidance.
  first
  | grind
  | sorry -- TODO: Establish one-step simulation from Flat.Step to Core.Step.
          -- KEY SUBGOAL: given `hstep : Flat.Step sf ev sf'` and converter success `h`,
          -- produce corresponding `sc sc'` with `Core.Step sc ev sc'`.

private theorem closureConvert_steps_simulation
    (s : Core.Program) (t : Flat.Program)
    (h : Flat.closureConvert s = .ok t) :
    ∀ (sf' : Flat.State) (tr : List Core.TraceEvent),
      Flat.Steps (Flat.initialState t) tr sf' →
      ∃ (sc' : Core.State), Core.Steps (Core.initialState s) tr sc' := by
  intro sf' tr hsteps
  -- This should be by induction on `hsteps` plus `closureConvert_step_simulation`.
  first
  | grind
  | sorry -- TODO: Lift one-step simulation to reflexive-transitive closure.
          -- KEY SUBGOAL: for `Flat.Steps (Flat.initialState t) tr sf'`, construct
          -- `sc'` with `Core.Steps (Core.initialState s) tr sc'`.

private theorem closureConvert_trace_reflection
    (s : Core.Program) (t : Flat.Program)
    (h : Flat.closureConvert s = .ok t) :
    ∀ b, Flat.Behaves t b → Core.Behaves s b := by
  intro b hb
  rcases hb with ⟨sf, hsteps, hhalt⟩
  have hsim := closureConvert_steps_simulation s t h sf b hsteps
  rcases hsim with ⟨scf, hcsteps⟩
  refine ⟨scf, hcsteps, ?_⟩
  -- Need to connect halting of the simulated Flat final state to Core final state.
  first
  | grind
  | sorry -- TODO: Prove simulated final Core state is halting.
          -- KEY SUBGOAL: from `hhalt : Flat.step? sf = none` and simulation relation,
          -- show `Core.step? scf = none`.

theorem closureConvert_correct (s : Core.Program) (t : Flat.Program)
    (h : Flat.closureConvert s = .ok t) :
    ∀ b, Flat.Behaves t b → ∃ b', Core.Behaves s b' ∧ b = b' :=
by
  intro b hb
  refine ⟨b, ?_, rfl⟩
  exact closureConvert_trace_reflection s t h b hb

end VerifiedJS.Proofs
