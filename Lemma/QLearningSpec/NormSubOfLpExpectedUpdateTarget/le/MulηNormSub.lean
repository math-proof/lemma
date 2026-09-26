import sympy.stats.q_learning
import sympy.Basic
import Lemma.QLearningSpec.ExpectedUpdateTarget.eq.ToLpAddMulSub
import Lemma.QLearningSpec.NormSubBellmanOp.le.MulNormSub
import Lemma.QLearningSpec.Gtμmin_0AndGeη_0AndLtη_1
open Finset


@[main]
private lemma main
  {S A : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype A] [DecidableEq A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
  {spec : QLearningSpec S A}
-- given
  (q q' : EuclideanVec (Fintype.card (S × A))) :
-- imply
  ‖WithLp.ofLp (spec.expected_update_target q) - WithLp.ofLp (spec.expected_update_target q')‖ ≤ spec.η * ‖WithLp.ofLp q - WithLp.ofLp q'‖ := by
-- proof
  have hμ : StochasticVec spec.MRP.μ := inferInstance
  have hγ := spec.hγ
  obtain ⟨-, hη, -⟩ := QLearningSpec.Gtμmin_0AndGeη_0AndLtη_1 (spec := spec)
  have hB := QLearningSpec.NormSubBellmanOp.le.MulNormSub (spec := spec) (WithLp.ofLp q) (WithLp.ofLp q')
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hη (norm_nonneg _))).2 fun i => ?_
  have hm0 := hμ.nonneg (QLearningSpec.fin_to_sa i)
  have hm1 : spec.MRP.μ (QLearningSpec.fin_to_sa i) ≤ 1 := by
    rw [← hμ.rowsum]
    exact single_le_sum (fun y _ => hμ.nonneg y) (mem_univ _)
  have hmin : spec.μmin ≤ spec.MRP.μ (QLearningSpec.fin_to_sa i) := inf'_le _ (mem_univ _)
  have e : (WithLp.ofLp (spec.expected_update_target q) - WithLp.ofLp (spec.expected_update_target q')) i =
      spec.MRP.μ (QLearningSpec.fin_to_sa i) * (spec.bellman_op (WithLp.ofLp q) - spec.bellman_op (WithLp.ofLp q')) i + (1 - spec.MRP.μ (QLearningSpec.fin_to_sa i)) * (WithLp.ofLp q - WithLp.ofLp q') i := by
    rw [QLearningSpec.ExpectedUpdateTarget.eq.ToLpAddMulSub, QLearningSpec.ExpectedUpdateTarget.eq.ToLpAddMulSub]
    simp only [Pi.sub_apply]
    ring
  have h₁ : |(spec.bellman_op (WithLp.ofLp q) - spec.bellman_op (WithLp.ofLp q')) i| ≤ spec.γ * ‖WithLp.ofLp q - WithLp.ofLp q'‖ := (norm_le_pi_norm _ i).trans hB
  have h₂ : |(WithLp.ofLp q - WithLp.ofLp q') i| ≤ ‖WithLp.ofLp q - WithLp.ofLp q'‖ := norm_le_pi_norm (WithLp.ofLp q - WithLp.ofLp q') i
  rw [e, Real.norm_eq_abs]
  calc _ ≤ _ := abs_add_le _ _
    _ = spec.MRP.μ (QLearningSpec.fin_to_sa i) * |(spec.bellman_op (WithLp.ofLp q) - spec.bellman_op (WithLp.ofLp q')) i| + (1 - spec.MRP.μ (QLearningSpec.fin_to_sa i)) * |(WithLp.ofLp q - WithLp.ofLp q') i| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hm0, abs_of_nonneg (sub_nonneg.2 hm1)]
    _ ≤ spec.MRP.μ (QLearningSpec.fin_to_sa i) * (spec.γ * ‖WithLp.ofLp q - WithLp.ofLp q'‖) + (1 - spec.MRP.μ (QLearningSpec.fin_to_sa i)) * ‖WithLp.ofLp q - WithLp.ofLp q'‖ :=
      add_le_add (mul_le_mul_of_nonneg_left h₁ hm0) (mul_le_mul_of_nonneg_left h₂ (sub_nonneg.2 hm1))
    _ = (1 - spec.MRP.μ (QLearningSpec.fin_to_sa i) * (1 - spec.γ)) * ‖WithLp.ofLp q - WithLp.ofLp q'‖ := by ring
    _ ≤ _ := by
      unfold QLearningSpec.η
      gcongr
      linarith


-- created on 2026-09-26
