import sympy.stats.q_learning
import sympy.Basic
import Lemma.Random.ExpectedUpdateTarget.eq.ToLpAddMulSub
import Lemma.Random.BellmanOpOfLpOptimalQ.eq.OfLpOptimalQ


@[main]
private lemma main
  {S A : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype A] [DecidableEq A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
  {spec : QLearningSpec S A} :
-- imply
  spec.expected_update_target spec.optimal_q = spec.optimal_q := by
-- proof
  rw [Random.ExpectedUpdateTarget.eq.ToLpAddMulSub, Random.BellmanOpOfLpOptimalQ.eq.OfLpOptimalQ, sub_self]
  ext i
  simp


-- created on 2026-09-26
