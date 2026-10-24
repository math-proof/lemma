import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TheoryOfProbability.code.Portmanteau
open MeasureTheory Filter ProbabilityTheory Set Function
open scoped Topology BoundedContinuousFunction ENNReal NNReal


namespace ProbabilityTheory

/--
[cdf_continuousAt_singleton_null](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/Portmanteau.lean)
-/
@[path]
lemma cdf_continuousAt_singleton_null
  {μ : Measure ℝ}
  [IsProbabilityMeasure μ]
  {x : ℝ}
-- given
  (hx : ContinuousAt (cdf μ) x) :
-- imply
  μ {x} = 0 := by
-- proof
  rw [← measure_cdf (μ := μ), StieltjesFunction.measure_singleton, ENNReal.ofReal_eq_zero]
  have : leftLim (↑(cdf μ)) x = (cdf μ) x := by
    have := (monotone_cdf μ).continuousAt_iff_leftLim_eq_rightLim.mp hx
    rwa [StieltjesFunction.rightLim_eq] at this
  linarith

end ProbabilityTheory

namespace ProbabilityTheory

/--
[cdf_continuousAt_frontier_Iic_null](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/Portmanteau.lean)
-/
@[path]
lemma cdf_continuousAt_frontier_Iic_null
  {μ : Measure ℝ}
  [IsProbabilityMeasure μ]
  {x : ℝ}
-- given
  (hx : ContinuousAt (cdf μ) x) :
-- imply
  μ (frontier (Iic x)) = 0 := by
-- proof
  rw [frontier_Iic]
  exact cdf_continuousAt_singleton_null μ x hx

end ProbabilityTheory

namespace ProbabilityTheory

/--
[probMeasure_Ioc_eq_toNNReal_cdf](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/Portmanteau.lean)
-/
@[path]
lemma probMeasure_Ioc_eq_toNNReal_cdf
  {ν : ProbabilityMeasure ℝ}
  {a b : ℝ} :
-- imply
  ν (Ioc a b) = (cdf (ν : Measure ℝ) b - cdf (ν : Measure ℝ) a).toNNReal := by
-- proof
  show ((ν : Measure ℝ) (Ioc a b)).toNNReal = _
  conv_lhs => rw [← measure_cdf (μ := (ν : Measure ℝ))]
  rw [StieltjesFunction.measure_Ioc]
  exact NNReal.eq rfl

end ProbabilityTheory

namespace ProbabilityTheory

/--
[dense_cdf_continuityPoints](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/Portmanteau.lean)
-/
@[path]
lemma dense_cdf_continuityPoints
  {μ : Measure ℝ}
  [IsProbabilityMeasure μ] :
-- imply
  Dense {x : ℝ | ContinuousAt (cdf μ) x} := by
-- proof
  have hcount : {x : ℝ | ¬ContinuousAt (↑(cdf μ)) x}.Countable :=
    (monotone_cdf μ).countable_not_continuousAt
  have hd := hcount.dense_compl (𝕜 := ℝ)
  rw [compl_setOf] at hd
  exact hd.mono fun x hx => not_not.mp hx

end ProbabilityTheory

namespace ProbabilityTheory

/--
[weakConvergence_iff_bounded_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/Portmanteau.lean)
-/
@[path]
lemma weakConvergence_iff_bounded_continuous
  {μs : ℕ → ProbabilityMeasure ℝ}
  {μ : ProbabilityMeasure ℝ} :
-- imply
  Tendsto μs atTop (𝓝 μ) ↔ (∀ f : ℝ →ᵇ ℝ, Tendsto (fun n ↦ ∫ x, f x ∂(μs n : Measure ℝ)) atTop (𝓝 (∫ x, f x ∂(μ : Measure ℝ)))) :=
-- proof
  ProbabilityMeasure.tendsto_iff_forall_integral_tendsto

end ProbabilityTheory


-- created on 2026-10-23
