import Mathlib
import sympy.Basic
import Def.v1.Atlas.GeometryOfManifolds.code.DonaldsonApproxHolomorphic
open Donaldson
open Real


namespace Donaldson

/--
[gaussian_pointwise_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/DonaldsonApproxHolomorphic.lean)
-/
@[path]
lemma gaussian_pointwise_le_one
  {X : CompactKahlerData}
  {X : CompactKahlerData}
  {k : ℕ}
  {p x : X.M} :
-- imply
  ‖(gaussianPeakSection X).section_ k p x‖ ≤ 1 := by
-- proof
  simp only [gaussianPeakSection]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (exp_pos _)]
  apply Real.exp_le_one_iff.mpr
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg' k
  nlinarith [sq_nonneg (@Dist.dist X.M X.metricInst.toDist p x)]

end Donaldson

namespace Donaldson

/--
[gaussian_peak_concentrated](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/DonaldsonApproxHolomorphic.lean)
-/
@[path]
lemma gaussian_peak_concentrated
  {X : CompactKahlerData}
  {X : CompactKahlerData} :
-- imply
  IsUniformlyConcentrated (gaussianPeakSection X) := by
-- proof
  refine ⟨(1 : ℝ), (1 : ℝ)/4, by norm_num, by norm_num, ?_⟩
  intro k p x
  simp only [gaussianPeakSection]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (exp_pos _)]
  have heq : -(↑k : ℝ) * (@Dist.dist X.M X.metricInst.toDist p x) ^ 2 / 4 =
    -(1/4 : ℝ) * ↑k * (@Dist.dist X.M X.metricInst.toDist p x) ^ 2 := by ring
  linarith [exp_pos (-(1/4 : ℝ) * ↑k * (@Dist.dist X.M X.metricInst.toDist p x) ^ 2),
    show exp (-(↑k : ℝ) * (@Dist.dist X.M X.metricInst.toDist p x) ^ 2 / 4) =
      exp (-(1/4 : ℝ) * ↑k * (@Dist.dist X.M X.metricInst.toDist p x) ^ 2) from
      congrArg exp heq]

end Donaldson

namespace Donaldson

/--
[gaussian_peak_lower_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/DonaldsonApproxHolomorphic.lean)
-/
@[path]
lemma gaussian_peak_lower_bound
  {X : CompactKahlerData}
  {X : CompactKahlerData} :
-- imply
  ∃ c : ℝ, c > 0 ∧ ∀ k : ℕ, 1 < k → ∀ p q : X.M, @Dist.dist X.M X.metricInst.toDist p q ≤ 1 / Real.sqrt (↑k) → c ≤ ‖(gaussianPeakSection X).section_ k p q‖ := by
-- proof
  refine ⟨Real.exp (-(1:ℝ)/4), exp_pos _, ?_⟩
  intro k hk p q hdist
  simp only [gaussianPeakSection]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (exp_pos _)]
  apply exp_le_exp.mpr
  have hk' : (0 : ℝ) < ↑k := Nat.cast_pos.mpr (Nat.lt_trans Nat.zero_lt_one hk)
  have hdist_nn : (0 : ℝ) ≤ @Dist.dist X.M X.metricInst.toDist p q :=
    @dist_nonneg X.M X.metricInst.toPseudoMetricSpace p q
  have hd_sq : (@Dist.dist X.M X.metricInst.toDist p q) ^ 2 ≤ 1 / ↑k := by
    have h2 : (@Dist.dist X.M X.metricInst.toDist p q) ^ 2 ≤ (1 / Real.sqrt ↑k) ^ 2 :=
      sq_le_sq' (by linarith) hdist
    calc _ ≤ (1 / Real.sqrt ↑k) ^ 2 := h2
      _ = 1 / (Real.sqrt ↑k) ^ 2 := by ring
      _ = 1 / ↑k := by rw [sq_sqrt (le_of_lt hk')]
  have hkd : (↑k : ℝ) * (@Dist.dist X.M X.metricInst.toDist p q) ^ 2 ≤ 1 :=
    calc (↑k : ℝ) * _ ≤ ↑k * (1 / ↑k) := mul_le_mul_of_nonneg_left hd_sq (le_of_lt hk')
      _ = 1 := by field_simp
  nlinarith
/-- Higher derivatives of the Gaussian peak section are uniformly bounded in the weighted norm. -/
end



-- created on 2026-10-23
