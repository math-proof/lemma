import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.RealAnalysis.code.FunctionSequences.PowerSeries
open Filter Topology FunctionSequences
open scoped NNReal ENNReal


namespace FunctionSequences

/--
[radiusOfConvergence_eq_formalRadius](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/FunctionSequences/PowerSeries.lean)
-/
@[path]
lemma radiusOfConvergence_eq_formalRadius
  {a : ℕ → ℝ} :
-- imply
  radiusOfConvergence a = (FormalMultilinearSeries.ofScalars ℝ a).radius := by
-- proof
  unfold radiusOfConvergence
  have heq : (fun n => ((‖a n‖₊ ^ (1 / (n : ℝ)) : ℝ≥0) : ℝ≥0∞)) =
    (fun n => ((‖FormalMultilinearSeries.ofScalars ℝ a n‖₊ ^ (1 / (n : ℝ)) : ℝ≥0) : ℝ≥0∞)) := by
    ext n; congr 1; congr 1
    simp only [FormalMultilinearSeries.ofScalars, nnnorm_smul]
    have h : ‖ContinuousMultilinearMap.mkPiAlgebraFin ℝ n ℝ‖₊ = 1 := by
      ext; simp [ContinuousMultilinearMap.norm_mkPiAlgebraFin]
    rw [h, mul_one]
  rw [heq, ← FormalMultilinearSeries.radius_inv_eq_limsup]
  exact inv_inv _

end FunctionSequences

namespace FunctionSequences

/--
[summable_abs_bounded](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/FunctionSequences/PowerSeries.lean)
-/
@[path]
lemma summable_abs_bounded
  {f : ℕ → ℝ}
-- given
  (hf : Summable f) :
-- imply
  ∃ C, ∀ n, := by
-- proof
  have htend := hf.tendsto_atTop_zero
  rw [Metric.tendsto_atTop] at htend
  obtain ⟨N, hN⟩ := htend 1 one_pos
  refine ⟨(∑ i ∈ Finset.range N, |f i|) + 1, fun n => ?_⟩
  by_cases hn : N ≤ n
  · have h1 := hN n hn
    rw [Real.dist_eq, sub_zero] at h1
    linarith [Finset.sum_nonneg (fun i _ => abs_nonneg (f i)) (s := Finset.range N)]
  · have hn' : n < N := not_le.mp hn
    calc |f n| ≤ ∑ i ∈ Finset.range N, |f i| :=
      Finset.single_le_sum (fun i _ => abs_nonneg (f i)) (Finset.mem_range.mpr hn')
      _ ≤ (∑ i ∈ Finset.range N, |f i|) + 1 := le_add_of_nonneg_right one_pos.le

end FunctionSequences

namespace FunctionSequences

/--
[le_radiusOfConvergence_of_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/FunctionSequences/PowerSeries.lean)
-/
@[path]
lemma le_radiusOfConvergence_of_bound
  {a : ℕ → ℝ}
  {r : NNReal}
  {C : ℝ}
-- given
  (h : ∀ n, |a n| * (r : ℝ) ^ n ≤ C) :
-- imply
  (r : ENNReal) ≤ radiusOfConvergence a := by
-- proof
  rw [radiusOfConvergence_eq_formalRadius]
  apply FormalMultilinearSeries.le_radius_of_bound _ C
  intro n
  simp only [FormalMultilinearSeries.ofScalars, norm_smul,
    ContinuousMultilinearMap.norm_mkPiAlgebraFin, mul_one, Real.norm_eq_abs]
  exact h n

end FunctionSequences

namespace FunctionSequences

/--
[summable_abs_mul_pow_of_lt_radius](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/FunctionSequences/PowerSeries.lean)
-/
@[path]
lemma summable_abs_mul_pow_of_lt_radius
  {a : ℕ → ℝ}
  {r : NNReal}
-- given
  (hr : (r : ENNReal) < radiusOfConvergence a) :
-- imply
  Summable (fun n => |a n| * (r : ℝ) ^ n) := by
-- proof
  rw [radiusOfConvergence_eq_formalRadius] at hr
  have h := (FormalMultilinearSeries.ofScalars ℝ a).summable_norm_mul_pow hr
  simp only [FormalMultilinearSeries.ofScalars, norm_smul,
    ContinuousMultilinearMap.norm_mkPiAlgebraFin, mul_one, Real.norm_eq_abs] at h
  exact h

end FunctionSequences

namespace FunctionSequences

/--
[power_series_uniform_convergence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/FunctionSequences/PowerSeries.lean)
-/
@[path]
lemma power_series_uniform_convergence
  {a : ℕ → ℝ}
  {x₀ : ℝ}
  {r : ℝ}
-- given
  (hr : 0 < r)
  (hr_lt : ENNReal.ofReal r < radiusOfConvergence a) :
-- imply
  TendstoUniformlyOn (fun n x => ∑ j ∈ Finset.range n, a j * (x - x₀) ^ j) (fun x => ∑' j, a j * (x - x₀) ^ j) Filter.atTop (Set.Icc (x₀ - r) (x₀ + r)) := by
-- proof
  set rnn : NNReal := ⟨r, hr.le⟩
  have hrnn_lt : (rnn : ENNReal) < radiusOfConvergence a := by
    simp only [rnn, ENNReal.ofReal_eq_coe_nnreal hr.le] at hr_lt ⊢
    exact hr_lt
  have hsum : Summable (fun j => |a j| * r ^ j) :=
    summable_abs_mul_pow_of_lt_radius a rnn hrnn_lt
  have hbound : ∀ j, ∀ x ∈ Set.Icc (x₀ - r) (x₀ + r),
    ‖a j * (x - x₀) ^ j‖ ≤ |a j| * r ^ j := by
    intro j x hx
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    gcongr
    have hx_bound : |x - x₀| ≤ r := by
      rw [abs_le]
      constructor
      · linarith [hx.1]
      · linarith [hx.2]
    exact hx_bound
  exact tendstoUniformlyOn_tsum_nat hsum hbound

end FunctionSequences


-- created on 2026-10-23
