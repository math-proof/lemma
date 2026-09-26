import sympy.stats.q_learning
import sympy.Basic
import Lemma.Matrix.Sum_Mul.eq.One.of.StochasticVec.RowStochastic
open Finset


@[main]
private lemma main
  {S A : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype A] [DecidableEq A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
  {spec : QLearningSpec S A}
-- given
  (q : EuclideanVec (Fintype.card (S × A))) :
-- imply
  spec.expected_update_target q = ∑ y, ∑ y', (spec.MRP.μ y * spec.MRP.P y y') • spec.update_target q (y, y') := by
-- proof
  simp only [QLearningSpec.expected_update_target, QLearningSpec.expected_update, QLearningSpec.update_target, Pi.add_apply, id, smul_add, sum_add_distrib, ← sum_smul,
    Matrix.Sum_Mul.eq.One.of.StochasticVec.RowStochastic (inferInstance : RowStochastic spec.MRP.P) (inferInstance : StochasticVec spec.MRP.μ), one_smul]


-- created on 2026-09-26
