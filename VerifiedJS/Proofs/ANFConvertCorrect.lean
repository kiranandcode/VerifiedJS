/-
  VerifiedJS — ANF Conversion Correctness Proof
  JS.Flat → JS.ANF semantic preservation.
-/

import VerifiedJS.ANF.Convert
import VerifiedJS.Flat.Semantics
import VerifiedJS.ANF.Semantics

namespace VerifiedJS.Proofs

private theorem anfConvert_step_simulation
    (s : Flat.Program) (t : ANF.Program)
    (h : ANF.convert s = .ok t) :
    ∀ (sa sa' : ANF.State) (ev : Core.TraceEvent),
      ANF.Step sa ev sa' →
      ∃ (sf sf' : Flat.State), Flat.Step sf ev sf' := by
  intro sa sa' ev hstep
  -- Automation-first pipeline requested in README/user guidance.
  first
  | grind
  | sorry -- TODO: Establish one-step simulation from ANF.Step to Flat.Step.
          -- KEY SUBGOAL: given `hstep : ANF.Step sa ev sa'` and converter success `h`,
          -- produce corresponding `sf sf'` with `Flat.Step sf ev sf'`.

private theorem anfConvert_steps_simulation
    (s : Flat.Program) (t : ANF.Program)
    (h : ANF.convert s = .ok t) :
    ∀ (sa' : ANF.State) (tr : List Core.TraceEvent),
      ANF.Steps (ANF.initialState t) tr sa' →
      ∃ (sf' : Flat.State), Flat.Steps (Flat.initialState s) tr sf' := by
  intro sa' tr hsteps
  -- This should be by induction on `hsteps` plus `anfConvert_step_simulation`.
  first
  | grind
  | sorry -- TODO: Lift one-step simulation to reflexive-transitive closure.
          -- KEY SUBGOAL: for `ANF.Steps (ANF.initialState t) tr sa'`, construct
          -- `sf'` with `Flat.Steps (Flat.initialState s) tr sf'`.

private theorem anfConvert_trace_reflection
    (s : Flat.Program) (t : ANF.Program)
    (h : ANF.convert s = .ok t) :
    ∀ b, ANF.Behaves t b → Flat.Behaves s b := by
  intro b hb
  rcases hb with ⟨sa, hsteps, hhalt⟩
  have hsim := anfConvert_steps_simulation s t h sa b hsteps
  rcases hsim with ⟨sf, hfsteps⟩
  refine ⟨sf, hfsteps, ?_⟩
  -- Need to connect halting of ANF final state to Flat final state.
  first
  | grind
  | sorry -- TODO: Prove simulated final Flat state is halting.
          -- KEY SUBGOAL: from `hhalt : ANF.step? sa = none` and simulation relation,
          -- show `Flat.step? sf = none`.

theorem anfConvert_correct (s : Flat.Program) (t : ANF.Program)
    (h : ANF.convert s = .ok t) :
    ∀ b, ANF.Behaves t b → ∃ b', Flat.Behaves s b' ∧ b = b' :=
by
  intro b hb
  refine ⟨b, ?_, rfl⟩
  exact anfConvert_trace_reflection s t h b hb

end VerifiedJS.Proofs
