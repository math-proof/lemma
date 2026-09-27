import sympy.stats.q_learning
import sympy.Basic
import Lemma.QLearningSpec.AbsSubMaxₐ.le.NormSub
import Lemma.Random.Sum.eq.One.of.ProbabilityMeasure
open Finset


@[main]
private lemma main
  {S A : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype A] [DecidableEq A] [MeasurableSpace A] [MeasurableSingletonClass A] [Nonempty A]
  {spec : QLearningSpec S A}
-- given
  (q q' : Fin (Fintype.card (S × A)) → ℝ) :
-- imply
  ‖spec.bellman_op q - spec.bellman_op q'‖ ≤ spec.γ * ‖q - q'‖ := by
-- proof
  have hγ := spec.hγ.1
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  have e : (spec.bellman_op q - spec.bellman_op q') i = spec.γ * ∑ s', (spec.P (QLearningSpec.fin_to_sa i) {s'} : ℝ) * (QLearningSpec.maxₐ q s' - QLearningSpec.maxₐ q' s') := by
    simp only [Pi.sub_apply, QLearningSpec.bellman_op, mul_sub, sum_sub_distrib]
    ring
  rw [e, Real.norm_eq_abs, abs_mul, abs_of_nonneg hγ]
  gcongr
  calc _ ≤ _ := abs_sum_le_sum_abs _ _
    _ ≤ ∑ s', (spec.P (QLearningSpec.fin_to_sa i) {s'} : ℝ) * ‖q - q'‖ := sum_le_sum fun s' _ => by
        rw [abs_mul, NNReal.abs_eq]
        gcongr
        exact QLearningSpec.AbsSubMaxₐ.le.NormSub q q' s'
    _ = _ := by rw [← sum_mul, Random.Sum.eq.One.of.ProbabilityMeasure, one_mul]


-- created on 2026-09-26
