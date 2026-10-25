import Mathlib
import sympy.Basic
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter9.SphericalCap
open Real Set MeasureTheory SphericalCap


namespace SphericalCap

/--
[sphericalCapMeasure_eq_zero_of_gt_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/SphericalCap.lean)
-/
@[path]
lemma sphericalCapMeasure_eq_zero_of_gt_one
  {n : ℕ}
  {ε : ℝ}
-- given
  (hε : ε > 1) :
-- imply
  sphericalCapMeasure n ε = 0 := by
-- proof
  unfold sphericalCapMeasure
  split
  case isTrue h =>
    unfold normalizedSphereMeasure
    have h_empty : {x : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) |
      (x : EuclideanSpace ℝ (Fin n)) ⟨0, h⟩ ≥ ε} = ∅ := by
      ext ⟨x, hx_mem⟩
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_le]
      rw [Metric.mem_sphere, dist_zero_right] at hx_mem
      have hx_norm : ‖x‖ = 1 := hx_mem
      have h_norm_sq : ‖x‖ ^ 2 = ∑ i : Fin n, ‖x i‖ ^ 2 :=
        EuclideanSpace.norm_sq_eq x
      have h1 : ‖x ⟨0, h⟩‖ ^ 2 ≤ ∑ i : Fin n, ‖x i‖ ^ 2 :=
        Finset.single_le_sum (f := fun i => ‖x i‖ ^ 2) (fun i _ => sq_nonneg _)
          (Finset.mem_univ (⟨0, h⟩ : Fin n))
      have h2 : ∑ i : Fin n, ‖x i‖ ^ 2 = 1 := by
        rw [← h_norm_sq, hx_norm]; norm_num
      have h3 : ‖x ⟨0, h⟩‖ ^ 2 ≤ 1 := by linarith
      have h4 : ‖x ⟨0, h⟩‖ ≤ 1 := by
        nlinarith [norm_nonneg (x ⟨0, h⟩)]
      have h5 : |x ⟨0, h⟩| ≤ 1 := by rwa [Real.norm_eq_abs] at h4
      linarith [le_abs_self (x ⟨0, h⟩)]
    rw [h_empty, show sphereVolume n ∅ = 0 from measure_empty]
    simp
  case isFalse => rfl

end SphericalCap

namespace SphericalCap

/--
[sqrt_one_sub_sq_le_exp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/SphericalCap.lean)
-/
@[path]
lemma sqrt_one_sub_sq_le_exp
  {ε : ℝ} :
-- imply
  Real.sqrt (1 - ε ^ 2) ≤ Real.exp (-(ε ^ 2 / 2)) := by
-- proof
  have h_key : 1 - ε ^ 2 ≤ Real.exp (-(ε ^ 2)) := by
    have h := Real.add_one_le_exp (-(ε ^ 2))
    linarith
  have h_sqrt_exp : Real.sqrt (Real.exp (-(ε ^ 2))) = Real.exp (-(ε ^ 2 / 2)) := by
    rw [← Real.exp_half (-(ε ^ 2))]
    ring_nf
  calc Real.sqrt (1 - ε ^ 2)
    ≤ Real.sqrt (Real.exp (-(ε ^ 2))) := Real.sqrt_le_sqrt h_key
    _ = Real.exp (-(ε ^ 2 / 2)) := h_sqrt_exp

end SphericalCap

namespace SphericalCap

/--
[inv_two_mul_le_exp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/SphericalCap.lean)
-/
@[path]
lemma inv_two_mul_le_exp
  {ε : ℝ}
-- given
  (hε_lb : 1 / Real.sqrt 2 ≤ ε)
  (hε_ub : ε ≤ 1) :
-- imply
  1 / (2 * ε) ≤ Real.exp (-(ε ^ 2 / 2)) := by
-- proof
  have hε_pos : (0 : ℝ) < ε := by
    have : (0 : ℝ) < 1 / Real.sqrt 2 := by positivity
    linarith
  have hsqrt2_sq : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (show (0:ℝ) ≤ 2 from by norm_num)
  have hsqrt2_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos_of_pos (by norm_num : (0:ℝ) < 2)
  have hε_sq_lb : (1 : ℝ) / 2 ≤ ε ^ 2 := by
    have h1 : (1 / Real.sqrt 2) * (1 / Real.sqrt 2) ≤ ε * ε :=
      mul_le_mul hε_lb hε_lb (by positivity) (le_of_lt hε_pos)
    have h2 : (1 / Real.sqrt 2) * (1 / Real.sqrt 2) = 1 / 2 := by
      rw [← sq, div_pow, one_pow, hsqrt2_sq]
    nlinarith
  suffices h_main : Real.exp (ε ^ 2 / 2) ≤ 2 * ε by
    have h_exp_inv : Real.exp (-(ε ^ 2 / 2)) = (Real.exp (ε ^ 2 / 2))⁻¹ := by
      rw [Real.exp_neg]
    rw [h_exp_inv, show (1 : ℝ) / (2 * ε) = (2 * ε)⁻¹ from one_div _]
    exact inv_anti₀ (Real.exp_pos _) h_main
  have hε2_half_nonneg : (0 : ℝ) ≤ ε ^ 2 / 2 := by positivity
  have hε2_half_lt_one : ε ^ 2 / 2 < 1 := by nlinarith
  have h_exp_bound : Real.exp (ε ^ 2 / 2) ≤ 1 / (1 - ε ^ 2 / 2) :=
    Real.exp_bound_div_one_sub_of_interval hε2_half_nonneg hε2_half_lt_one
  suffices h2 : 1 / (1 - ε ^ 2 / 2) ≤ 2 * ε from le_trans h_exp_bound h2
  have h_denom_pos : (0 : ℝ) < 1 - ε ^ 2 / 2 := by nlinarith
  rw [div_le_iff₀ h_denom_pos]
  nlinarith [sq_nonneg (1 - ε)]

end SphericalCap

namespace SphericalCap

/--
[pow_le_exp_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/SphericalCap.lean)
-/
@[path]
lemma pow_le_exp_of_le
  {r ε : ℝ}
  {n : ℕ}
-- given
  (hr : 0 ≤ r)
  (h : r ≤ Real.exp (-(ε ^ 2 / 2))) :
-- imply
  r ^ n ≤ Real.exp (-(↑n * ε ^ 2 / 2)) := by
-- proof
  calc r ^ n
    ≤ (Real.exp (-(ε ^ 2 / 2))) ^ n := pow_le_pow_left₀ hr h n
    _ = Real.exp (↑n * (-(ε ^ 2 / 2))) := by rw [← Real.exp_nat_mul]
    _ = Real.exp (-(↑n * ε ^ 2 / 2)) := by congr 1; ring
/-- **Spherical cap concentration** (Theorem 9.4.11). For a uniformly random unit vector
$x \sim S^{n-1}$ and $\varepsilon \ge 0$,
$\mathbb{P}(x_1 \ge \varepsilon) \le \exp(-n \varepsilon^{2}/2)$. -/
end SphericalCap
namespace SphericalCap

end SphericalCap

namespace SphericalCap

/--
[sphereVolume_pos_of_normalizedSphereMeasure_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/SphericalCap.lean)
-/
@[path]
lemma sphereVolume_pos_of_normalizedSphereMeasure_pos
  {n : ℕ}
  {A : Set (↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1))}
-- given
  (h : normalizedSphereMeasure A > 0) :
-- imply
  sphereVolume n Set.univ ≠ 0 := by
-- proof
  intro h0
  have : normalizedSphereMeasure A = 0 := by
    unfold normalizedSphereMeasure
    have : (sphereVolume n Set.univ).toReal = 0 :=
      (ENNReal.toReal_eq_zero_iff _).mpr (Or.inl h0)
    rw [this, div_zero]
  linarith

end SphericalCap

namespace SphericalCap

/--
[normalizedSphereMeasure_nonempty_of_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/SphericalCap.lean)
-/
@[path]
lemma normalizedSphereMeasure_nonempty_of_pos
  {n : ℕ}
  {A : Set (↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1))}
-- given
  (h : normalizedSphereMeasure A > 0) :
-- imply
  A.Nonempty := by
-- proof
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  have : normalizedSphereMeasure A = 0 := by
    unfold normalizedSphereMeasure
    rw [hempty, measure_empty, ENNReal.toReal_zero, zero_div]
  linarith
/-- Key intermediate step in the concentration of measure on $S^{n-1}$: if $\mu(A) \ge 1/2$,
then $1 - \mu(A_t) \le \mathbb{P}\!\big(x_1 \ge t/\sqrt{2}\big)$ for every $t \ge 0$,
obtained from Lévy's isoperimetric inequality. -/

end SphericalCap


-- created on 2026-10-23
