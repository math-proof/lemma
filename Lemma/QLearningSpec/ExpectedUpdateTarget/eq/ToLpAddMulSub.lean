import sympy.stats.q_learning
import sympy.Basic
import Lemma.FiniteMDP.PMRP.eq.MulPPi
import Lemma.Random.Sum.eq.One.of.ProbabilityMeasure
open Finset


@[main]
private lemma main
  {S A : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype A] [DecidableEq A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
  {spec : QLearningSpec S A}
-- given
  (q : EuclideanVec (Fintype.card (S × A))) :
-- imply
  spec.expected_update_target q = WithLp.toLp 2 (fun i => spec.MRP.μ (QLearningSpec.fin_to_sa i) * (spec.bellman_op (WithLp.ofLp q) - WithLp.ofLp q) i + q i) := by
-- proof
  have hP : RowStochastic spec.MRP.P := inferInstance
  have hx : ∀ (y : S × A) (i : Fin (Fintype.card (S × A))), QLearningSpec.x y i = if y = QLearningSpec.fin_to_sa i then 1 else 0 := fun y i => by
    rw [show QLearningSpec.x y i = (EuclideanSpace.single (QLearningSpec.sa_to_fin y) (1 : ℝ)) i from rfl, PiLp.single_apply]
    by_cases h : y = QLearningSpec.fin_to_sa i
    · rw [if_pos h, if_pos (by rw [h, QLearningSpec.sa_to_fin, QLearningSpec.fin_to_sa, Equiv.apply_symm_apply])]
    · rw [if_neg h, if_neg fun h' => h (by rw [h', QLearningSpec.fin_to_sa, QLearningSpec.sa_to_fin, Equiv.symm_apply_apply])]
  ext i
  have hi : QLearningSpec.sa_to_fin (QLearningSpec.fin_to_sa i) = i := by
    rw [QLearningSpec.sa_to_fin, QLearningSpec.fin_to_sa, Equiv.apply_symm_apply]
  have hsum : ∑ y', spec.MRP.P (QLearningSpec.fin_to_sa i) y' * QLearningSpec.maxₐ (WithLp.ofLp q) y'.1 = ∑ s', (spec.P (QLearningSpec.fin_to_sa i) {s'} : ℝ) * QLearningSpec.maxₐ (WithLp.ofLp q) s' := by
    rw [Fintype.sum_prod_type]
    refine sum_congr rfl fun s' _ => ?_
    simp only [FiniteMDP.PMRP.eq.MulPPi]
    rw [← sum_mul, ← mul_sum, Random.Sum.eq.One.of.ProbabilityMeasure, mul_one]
  rw [QLearningSpec.expected_update_target, Pi.add_apply, id, PiLp.add_apply, PiLp.toLp_apply]
  congr 1
  simp only [QLearningSpec.expected_update, WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, QLearningSpec.update, hx, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (QLearningSpec.fin_to_sa i) (fun y _ hy => sum_eq_zero fun y' _ => if_neg hy) (fun h => absurd (mem_univ _) h)]
  simp only [if_true, hi]
  calc _ = spec.MRP.μ (QLearningSpec.fin_to_sa i) * (spec.r (QLearningSpec.fin_to_sa i) * ∑ y', spec.MRP.P (QLearningSpec.fin_to_sa i) y' + spec.γ * ∑ y', spec.MRP.P (QLearningSpec.fin_to_sa i) y' * QLearningSpec.maxₐ (WithLp.ofLp q) y'.1 - q i * ∑ y', spec.MRP.P (QLearningSpec.fin_to_sa i) y') := by
        simp only [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
        exact sum_congr rfl fun y' _ => by ring
    _ = _ := by
      rw [(hP.stochastic _).rowsum, hsum, Pi.sub_apply, QLearningSpec.bellman_op]
      ring


-- created on 2026-09-26
