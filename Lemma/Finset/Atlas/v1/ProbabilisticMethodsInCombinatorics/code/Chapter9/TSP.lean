import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter9.TSP
open MeasureTheory Real BigOperators Finset ENNReal Set TSPConcentration


namespace TSPConcentration

/--
[sum_inv_sub_le_log](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/TSP.lean)
-/
@[path]
lemma sum_inv_sub_le_log
  {n : ℕ} :
-- imply
  ∑ i ∈ Finset.range n, (1 : ℝ) / (↑(n - i) : ℝ) ≤ 1 + Real.log ↑n := by
-- proof
  by_cases hn : n = 0
  · simp [hn]
  suffices h : ∑ i ∈ Finset.range n, (1 : ℝ) / (↑(n - i) : ℝ) = (harmonic n : ℝ) by
    rw [h]; exact_mod_cast harmonic_le_one_add_log n
  simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  simp_rw [one_div]
  apply Finset.sum_nbij' (fun i => n - 1 - i) (fun k => n - 1 - k)
  · intro i hi; exact Finset.mem_range.mpr (by have := Finset.mem_range.mp hi; omega)
  · intro k hk; exact Finset.mem_range.mpr (by have := Finset.mem_range.mp hk; omega)
  · intro i hi; have := Finset.mem_range.mp hi; omega
  · intro k hk; have := Finset.mem_range.mp hk; omega
  · intro i hi
    have hi' : i < n := Finset.mem_range.mp hi
    congr 1; exact_mod_cast show n - i = (n - 1 - i) + 1 from by omega

end TSPConcentration

namespace TSPConcentration

/--
[azuma_variance_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/TSP.lean)
-/
@[path]
lemma azuma_variance_bound
  {n : ℕ}
  {C : ℝ} :
-- imply
  ∑ i ∈ Finset.range n, (C / Real.sqrt (↑(n - i) : ℝ)) ^ 2 ≤ C ^ 2 * (1 + Real.log ↑n) := by
-- proof
  by_cases hn : n = 0
  · simp [hn]; positivity
  have h_terms : ∀ i ∈ Finset.range n, (C / Real.sqrt (↑(n - i) : ℝ)) ^ 2 =
    C ^ 2 * (1 / (↑(n - i) : ℝ)) := by
    intro i hi
    have hi_lt : i < n := Finset.mem_range.mp hi
    have h_pos : (0 : ℝ) < ↑(n - i) := by exact_mod_cast Nat.sub_pos_of_lt hi_lt
    rw [div_pow, sq_sqrt (le_of_lt h_pos)]; ring
  rw [Finset.sum_congr rfl h_terms, ← Finset.mul_sum]
  gcongr
  exact sum_inv_sub_le_log n

end TSPConcentration

namespace TSPConcentration

/--
[rhee_talagrand_tsp_concentration](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/TSP.lean)
-/
@[path]
lemma rhee_talagrand_tsp_concentration
  [MeasurableSpace Ω]
  {μ : MeasureTheory.Measure Ω}
  [IsProbabilityMeasure μ]
  {n : ℕ}
  {L : Ω → ℝ}
  {C : ℝ}
-- given
  (hn : 2 ≤ n)
  (hC : 0 < C)
  (hAzuma : ∀ t : ℝ, 0 ≤ t → μ {ω | t ≤ |L ω - ∫ ω', L ω' ∂μ|} ≤ ENNReal.ofReal (2 * exp (-(t ^ 2 / (2 * (∑ i ∈ Finset.range n, (C / Real.sqrt (↑(n - i) : ℝ)) ^ 2)))))) :
-- imply
  IsSubGaussianAboutMean L (Real.sqrt (2 * C ^ 2 * (1 + Real.log ↑n))) μ := by
-- proof
  intro t ht
  have hlog_pos : (0 : ℝ) < Real.log (↑n : ℝ) :=
    Real.log_pos (by exact_mod_cast show (1 : ℕ) < n from by omega)
  have h_denom_pos : (0 : ℝ) < 2 * C ^ 2 * (1 + Real.log ↑n) := by positivity
  have hbd := hAzuma t ht
  have h_var := azuma_variance_bound n C
  calc μ {ω | t ≤ |L ω - ∫ ω', L ω' ∂μ|}
    ≤ ENNReal.ofReal (2 * exp (-(t ^ 2 /
      (2 * (∑ i ∈ Finset.range n, (C / Real.sqrt (↑(n - i) : ℝ)) ^ 2))))) := hbd
    _ ≤ ENNReal.ofReal (2 * exp (-(t ^ 2 /
      (2 * C ^ 2 * (1 + Real.log ↑n))))) := by
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
      apply Real.exp_le_exp.mpr
      apply neg_le_neg
      apply div_le_div_of_nonneg_left (sq_nonneg t)
      · have h_sum_pos : (0 : ℝ) < ∑ i ∈ Finset.range n,
        (C / Real.sqrt (↑(n - i) : ℝ)) ^ 2 := by
        apply Finset.sum_pos
        · intro i hi
          have hi_lt : i < n := Finset.mem_range.mp hi
          have h_pos : (0 : ℝ) < ↑(n - i) := by exact_mod_cast Nat.sub_pos_of_lt hi_lt
          positivity
        · exact ⟨0, Finset.mem_range.mpr (by omega)⟩
        positivity
      · linarith [h_var]
    _ = ENNReal.ofReal (2 * exp (-(t ^ 2 /
      (Real.sqrt (2 * C ^ 2 * (1 + Real.log ↑n))) ^ 2))) := by
      congr 1; congr 1; congr 1; congr 1
      rw [sq_sqrt (le_of_lt h_denom_pos)]

end TSPConcentration


-- created on 2026-10-23
