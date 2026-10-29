import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.TheoryOfProbability.code.CenteredConvergence
open MeasureTheory ProbabilityTheory Filter Finset ENNReal KolmogorovThreeSeries


namespace KolmogorovThreeSeries

/--
[eLpNorm_one_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/CenteredConvergence.lean)
-/
@[path]
lemma eLpNorm_one_le_two
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {f : Ω → ℝ}
-- given
  (hf : AEStronglyMeasurable f μ) :
-- imply
  eLpNorm f 1 μ ≤ eLpNorm f 2 μ := by
-- proof
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2)
    (by norm_num : (1 : ENNReal) ≤ 2) hf
  simp only [measure_univ, one_rpow, mul_one] at h
  exact h
set_option maxHeartbeats 800000 in

end KolmogorovThreeSeries

namespace KolmogorovThreeSeries

/--
[eLpNorm_one_le_sqrt_integral_sq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/CenteredConvergence.lean)
-/
@[path]
lemma eLpNorm_one_le_sqrt_integral_sq
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {f : Ω → ℝ}
  {C : ℝ}
-- given
  (hf : MemLp f 2 μ)
  (h_int_sq : ∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ ≤ C) :
-- imply
  eLpNorm f 1 μ ≤ ENNReal.ofReal (Real.sqrt C) := by
-- proof
  have h1 : eLpNorm f 1 μ ≤ eLpNorm f 2 μ := eLpNorm_one_le_two hf.aestronglyMeasurable
  have h2 : eLpNorm f 2 μ ≤ ENNReal.ofReal (Real.sqrt C) := by
    rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num : (2 : ENNReal) ≠ 0) (by norm_num : (2 : ENNReal) ≠ ⊤)]
    apply ENNReal.ofReal_le_ofReal
    simp only [ENNReal.toReal_ofNat]
    rw [Real.sqrt_eq_rpow]
    show (∫ (a : Ω), ‖f a‖ ^ (2 : ℝ) ∂μ) ^ (2 : ℝ)⁻¹ ≤ C ^ ((1 : ℝ) / 2)
    rw [show (2 : ℝ)⁻¹ = (1 : ℝ) / 2 from by norm_num]
    exact Real.rpow_le_rpow (integral_nonneg (fun x => by positivity)) h_int_sq (by norm_num)
  exact h1.trans h2
set_option linter.unusedSectionVars false in
set_option maxHeartbeats 6400000 in

end KolmogorovThreeSeries

namespace KolmogorovThreeSeries

/--
[ae_tendsto_sum_of_indep_centered_L1bdd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/CenteredConvergence.lean)
-/
@[path]
lemma ae_tendsto_sum_of_indep_centered_L1bdd
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {Z : ℕ → Ω → ℝ}
  {R : NNReal}
-- given
  (hZ_sm : ∀ n, StronglyMeasurable (Z n))
  (hZ_indep : iIndepFun (m := fun _ => inferInstance) Z μ)
  (hZ_mean : ∀ n, ∫ ω, Z n ω ∂μ = 0)
  (hZ_int : ∀ n, Integrable (Z n) μ)
  (hZ_L1_bdd : ∀ n, eLpNorm (fun ω => ∑ k ∈ range (n + 1), Z k ω) 1 μ ≤ ↑R) :
-- imply
  ∀ᵐ ω ∂μ, ∃ c, Tendsto (fun n => ∑ k ∈ range (n + 1), Z k ω) atTop (nhds c) := by
-- proof
  set ℱ := Filtration.natural (β := fun _ : ℕ => ℝ) Z hZ_sm
  have sum_eq : ∀ n, (fun ω => ∑ k ∈ range (n + 1), Z k ω) = ∑ k ∈ range (n + 1), Z k := by
    intro n; ext ω; simp [Finset.sum_apply]
  have hS_int : ∀ n, Integrable (fun ω => ∑ k ∈ range (n + 1), Z k ω) μ := fun n =>
    integrable_finset_sum _ (fun k _ => hZ_int k)
  have hS_sm_m : ∀ n, StronglyMeasurable[ℱ n] (fun ω => ∑ k ∈ range (n + 1), Z k ω) := by
    intro n; rw [sum_eq]
    exact stronglyMeasurable_sum _ (fun k hk => by
      have hkn : k ≤ n := by have := Finset.mem_range.mp hk; omega
      exact (Filtration.stronglyAdapted_natural hZ_sm k).mono (ℱ.mono hkn))
  have hS_mart : Martingale (fun n ω => ∑ k ∈ range (n + 1), Z k ω) ℱ μ := by
    apply martingale_nat (fun n => hS_sm_m n) hS_int
    intro i
    have heq_add : (fun ω => ∑ k ∈ range (i + 2), Z k ω) =
      (fun ω => ∑ k ∈ range (i + 1), Z k ω) + Z (i + 1) := by
      ext ω; simp [sum_range_succ, Pi.add_apply]
    rw [heq_add]
    have hce := condExp_add (hS_int i) (hZ_int (i + 1)) (ℱ i : MeasurableSpace Ω)
    have hSi_ce : μ[fun ω => ∑ k ∈ range (i + 1), Z k ω | (ℱ i : MeasurableSpace Ω)] =
      fun ω => ∑ k ∈ range (i + 1), Z k ω :=
      condExp_of_stronglyMeasurable (ℱ.le i) (hS_sm_m i) (hS_int i)
    have hZi1_ce : μ[Z (i + 1) | (ℱ i : MeasurableSpace Ω)] =ᵐ[μ] fun _ => (0 : ℝ) := by
      have h := hZ_indep.condExp_natural_ae_eq_of_lt hZ_sm (show i < i + 1 by omega)
      simpa [hZ_mean (i + 1)] using h
    filter_upwards [hce, hZi1_ce] with ω hω1 hω3
    simp only [Pi.add_apply] at hω1
    rw [hSi_ce] at hω1
    linarith
  exact hS_mart.submartingale.exists_ae_tendsto_of_bdd (R := R) hZ_L1_bdd

end KolmogorovThreeSeries


-- created on 2026-10-23
