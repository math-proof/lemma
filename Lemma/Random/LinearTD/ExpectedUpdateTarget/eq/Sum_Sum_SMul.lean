import sympy.stats.linear_td
import sympy.Basic
import Lemma.Matrix.Sum_Mul.eq.One.of.StochasticVec.RowStochastic
open Finset


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]
  {d : ℕ}
  {spec : LinearTDSpec S d}
-- given
  (w : EuclideanVec d) :
-- imply
  spec.expected_update_target w = ∑ s, ∑ s', (spec.μ s * spec.P s s') • spec.update_target w (s, s') := by
-- proof
  simp only [LinearTDSpec.expected_update_target, LinearTDSpec.expected_update, LinearTDSpec.update_target, Pi.add_apply, id, smul_add, sum_add_distrib, ← sum_smul,
    Matrix.Sum_Mul.eq.One.of.StochasticVec.RowStochastic (inferInstance : RowStochastic spec.P) (inferInstance : StochasticVec spec.μ), one_smul]


-- created on 2026-09-26
