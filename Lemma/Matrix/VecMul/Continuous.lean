import sympy.Basic
import sympy.stats.stochastic_process_types
import Mathlib.Topology.Instances.Matrix
open WithLp PiLp
open scoped Matrix


@[main]
private lemma main
  {S : Type*} [Fintype S]
-- given
  (P : Matrix S S ℝ) :
-- imply
  Continuous fun v : l1Space S => ofL1 (WithLp.ofLp v ᵥ* P) := by
-- proof
  apply (continuous_toLp (p := (1 : ENNReal)) (β := fun _ : S => ℝ)).comp
  apply (Continuous.matrix_vecMul continuous_id continuous_const).comp
  apply continuous_ofLp (p := (1 : ENNReal)) (β := fun _ : S => ℝ)


-- created on 2026-09-22
-- updated on 2026-09-26
