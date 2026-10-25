import Mathlib
import sympy.Basic
import Def.v1.Atlas.ProjectionTheory.code.ProjectionSmoothing
open MeasureTheory MeasureTheory.Measure Metric Set Function Filter ProjectionSmoothing


namespace ProjectionSmoothing

/--
[sobolevNormSq_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/ProjectionSmoothing.lean)
-/
@[path]
lemma sobolevNormSq_nonneg
  {s : ℝ}
  {g : ℝ → ℂ} :
-- imply
  0 ≤ sobolevNormSq s g := by
-- proof
  apply integral_nonneg
  intro ξ
  positivity

end ProjectionSmoothing

namespace ProjectionSmoothing

/--
[cauchy_schwarz_compact_support](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/ProjectionSmoothing.lean)
-/
@[path]
lemma cauchy_schwarz_compact_support
  {d : ℕ}
  {f : EuclideanSpace ℝ (Fin d) → ℂ}
-- given
  (hf_l2 : MemLp f 2 volume)
  (hf_supp : support f ⊆ closedBall 0 1) :
-- imply
  (∫ x : EuclideanSpace ℝ (Fin d), ‖f x‖ ∂volume) ^ 2 ≤ (volume (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal * ∫ x : EuclideanSpace ℝ (Fin d), ‖f x‖ ^ 2 ∂volume := by
-- proof
  set g : EuclideanSpace ℝ (Fin d) → ℂ := (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1).indicator (fun _ => 1)
  have h_eq : ∀ x, ‖f x‖ = ‖f x‖ * ‖g x‖ := by
    intro x
    by_cases hx : x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1
    · simp [g, indicator_of_mem hx]
    · have hx' : x ∉ support f := fun h => hx (hf_supp h)
      simp [mem_support] at hx'
      rw [hx', norm_zero, zero_mul]
  have h_holder : (2 : ℝ).HolderConjugate 2 := by constructor <;> norm_num
  have hf_memLp : MemLp f (ENNReal.ofReal 2) volume := by
    rwa [show ENNReal.ofReal (2 : ℝ) = 2 from by simp [ENNReal.ofReal]]
  have hg_memLp : MemLp g (ENNReal.ofReal 2) volume := by
    rw [show ENNReal.ofReal (2 : ℝ) = 2 from by simp [ENNReal.ofReal]]
    exact memLp_indicator_const 2 measurableSet_closedBall 1
      (Or.inr measure_closedBall_lt_top.ne)
  have h_ineq := integral_mul_norm_le_Lp_mul_Lq h_holder hf_memLp hg_memLp
  have h_g_integral : ∫ x : EuclideanSpace ℝ (Fin d), ‖g x‖ ^ (2 : ℝ) ∂volume =
    (volume (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal := by
    have h1 : (fun x => ‖g x‖ ^ (2 : ℝ)) = (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1).indicator (fun _ => (1 : ℝ)) := by
      ext x
      by_cases hx : x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1
      · simp [g, indicator_of_mem hx]
      · simp [g, indicator_of_notMem hx, norm_zero,
        Real.zero_rpow (show (2:ℝ) ≠ 0 from by norm_num)]
    rw [h1, integral_indicator measurableSet_closedBall, integral_const]
    simp [Measure.real]
  suffices h : (∫ x, ‖f x‖ ∂volume) ^ 2 ≤
    (volume (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal *
      ∫ x, ‖f x‖ ^ (2 : ℝ) ∂volume by
    convert h using 2
    congr 1; ext x; norm_cast
  rw [show ∫ x, ‖f x‖ ∂volume = ∫ x, ‖f x‖ * ‖g x‖ ∂volume from by
    congr 1; ext x; exact h_eq x]
  have h_f_int_nonneg : 0 ≤ ∫ x : EuclideanSpace ℝ (Fin d), ‖f x‖ ^ (2 : ℝ) ∂volume :=
    integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _)
  have h_g_int_nonneg : 0 ≤ ∫ x : EuclideanSpace ℝ (Fin d), ‖g x‖ ^ (2 : ℝ) ∂volume :=
    integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _)
  have h_product_nonneg : 0 ≤ ∫ x : EuclideanSpace ℝ (Fin d), ‖f x‖ * ‖g x‖ ∂volume :=
    integral_nonneg (fun x => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  calc (∫ x, ‖f x‖ * ‖g x‖ ∂volume) ^ 2
    ≤ ((∫ x, ‖f x‖ ^ (2:ℝ) ∂volume) ^ ((1:ℝ)/2) * (∫ x, ‖g x‖ ^ (2:ℝ) ∂volume) ^ ((1:ℝ)/2)) ^ 2 := by
      apply sq_le_sq' (by linarith) h_ineq
    _ = (∫ x, ‖f x‖ ^ (2:ℝ) ∂volume) * (∫ x, ‖g x‖ ^ (2:ℝ) ∂volume) := by
      rw [mul_pow, ← Real.rpow_natCast ((∫ x, ‖f x‖ ^ (2:ℝ) ∂volume) ^ ((1:ℝ)/2)) 2,
        ← Real.rpow_natCast ((∫ x, ‖g x‖ ^ (2:ℝ) ∂volume) ^ ((1:ℝ)/2)) 2,
        ← Real.rpow_mul h_f_int_nonneg, ← Real.rpow_mul h_g_int_nonneg]
      norm_num
    _ = (volume (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal *
      (∫ x, ‖f x‖ ^ (2:ℝ) ∂volume) := by
      rw [h_g_integral]; ring
/-- For `f ∈ L²(ℝ^d)` supported in the unit ball, the spherical average of
`‖π_θ f‖_{H^{(d−1)/2}}²` is controlled by a constant times `‖f‖_{L²}²`. -/

end ProjectionSmoothing


-- created on 2026-10-23
