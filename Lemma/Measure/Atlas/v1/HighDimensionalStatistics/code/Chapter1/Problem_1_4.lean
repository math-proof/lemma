import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter1.Problem_1_4
open MeasureTheory Real ProbabilityTheory Problem_1_4


namespace Problem_1_4

/--
[integral_exp_sub_one_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Problem_1_4.lean)
-/
@[path]
lemma integral_exp_sub_one_sub
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {f : Ω → ℝ}
-- given
  (hf : Integrable f μ)
  (hef : Integrable (fun ω => Real.exp (f ω)) μ)
  (hmean : ∫ ω, f ω ∂μ = 0) :
-- imply
  ∫ ω, (Real.exp (f ω) - 1 - f ω) ∂μ = ∫ ω, Real.exp (f ω) ∂μ - 1 := by
-- proof
  calc ∫ ω, (Real.exp (f ω) - 1 - f ω) ∂μ
    = ∫ ω, ((fun ω => Real.exp (f ω) - 1) ω - f ω) ∂μ := by ring_nf
    _ = ∫ ω, (fun ω => Real.exp (f ω) - 1) ω ∂μ - ∫ ω, f ω ∂μ :=
      integral_sub (hef.sub (integrable_const 1)) hf
    _ = _ := by
      rw [hmean, sub_zero]
      show ∫ ω, (Real.exp (f ω) - 1) ∂μ = _
      calc ∫ ω, (Real.exp (f ω) - 1) ∂μ
        = ∫ ω, ((fun ω => Real.exp (f ω)) ω - (fun _ => (1:ℝ)) ω) ∂μ := by ring_nf
        _ = _ := by
          rw [integral_sub hef (integrable_const 1)]
          simp [integral_const]

end Problem_1_4

namespace Problem_1_4

/--
[subgaussian_zero_ae](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Problem_1_4.lean)
-/
@[path]
lemma subgaussian_zero_ae
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {X : Ω → ℝ}
-- given
  (hSG : IsSubGaussian X 0 μ) :
-- imply
  X =ᵐ[μ] 0 := by
-- proof
  obtain ⟨hint, hmean, hexp_int, hmgf⟩ := hSG
  have hmgf1 : ∀ s, ∫ ω, Real.exp (s * X ω) ∂μ ≤ 1 := by
    intro s; have := hmgf s; simp at this; exact this
  have hexp_int1 : Integrable (fun ω => Real.exp (X ω)) μ := by
    have := hexp_int 1; simp only [one_mul] at this; exact this
  have hg_nonneg : ∀ ω, 0 ≤ Real.exp (X ω) - 1 - X ω := by
    intro ω; linarith [add_one_le_exp (X ω)]
  have hg_int : Integrable (fun ω => Real.exp (X ω) - 1 - X ω) μ :=
    (hexp_int1.sub (integrable_const 1)).sub hint
  have hg_integral := integral_exp_sub_one_sub hint hexp_int1 hmean
  have h_le : ∫ ω, Real.exp (X ω) ∂μ ≤ 1 := by
    have := hmgf1 1; simp only [one_mul] at this; exact this
  have h_ge : 1 ≤ ∫ ω, Real.exp (X ω) ∂μ := by
    have hJ := convexOn_exp.map_integral_le continuousOn_exp isClosed_univ
      (by simp) hint hexp_int1
    rw [hmean] at hJ; simp at hJ; exact hJ
  have hg_zero : ∫ ω, (Real.exp (X ω) - 1 - X ω) ∂μ = 0 := by
    rw [hg_integral]; linarith
  have hg_ae : (fun ω => Real.exp (X ω) - 1 - X ω) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall hg_nonneg) hg_int).mp hg_zero
  exact hg_ae.mono fun ω hω => by
    simp only [Pi.zero_apply] at hω
    have : Real.exp (X ω) = 1 + X ω := by linarith
    by_contra hne
    exact absurd this (ne_of_gt (by linarith [add_one_lt_exp hne]))

end Problem_1_4


-- created on 2026-10-23
