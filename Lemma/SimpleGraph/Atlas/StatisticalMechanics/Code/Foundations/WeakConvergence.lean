import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Foundations.WeakConvergence
open MeasureTheory Filter Topology BoundedContinuousFunction StatMech


/--
[weakConvergesTo_iff_forall_integral_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/WeakConvergence.lean)
-/
@[path]
private lemma weakConvergesTo_iff_forall_integral_tendsto_eq
  [Countable E]
  {μ : ℕ → ProbabilityMeasure (ConfigSpace E)}
  {ν : ProbabilityMeasure (ConfigSpace E)} :
-- imply
  WeakConvergesTo μ ν ↔ ∀ f : (ConfigSpace E) →ᵇ ℝ, Tendsto (fun n => ∫ x, f x ∂(μ n : Measure (ConfigSpace E))) atTop (𝓝 (∫ x, f x ∂(ν : Measure (ConfigSpace E)))) := by
-- proof
  apply StatMech.weakConvergesTo_iff_forall_integral_tendsto μ ν

/--
[weakConvergesTo_iff_forall_lintegral_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/WeakConvergence.lean)
-/
@[path]
private lemma weakConvergesTo_iff_forall_lintegral_tendsto_eq
  [Countable E]
  {μ : ℕ → ProbabilityMeasure (ConfigSpace E)}
  {ν : ProbabilityMeasure (ConfigSpace E)} :
-- imply
  WeakConvergesTo μ ν ↔ ∀ f : (ConfigSpace E) →ᵇ ℝ≥0, Tendsto (fun n => ∫⁻ x, f x ∂(μ n : Measure (ConfigSpace E))) atTop (𝓝 (∫⁻ x, f x ∂(ν : Measure (ConfigSpace E)))) := by
-- proof
  apply StatMech.weakConvergesTo_iff_forall_lintegral_tendsto μ ν

/--
[WeakConvergesTo.tendsto_integral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/WeakConvergence.lean)
-/
@[path]
private lemma tendsto_integral_eq
  [Countable E]
  {μ : ℕ → ProbabilityMeasure (ConfigSpace E)}
  {ν : ProbabilityMeasure (ConfigSpace E)}
  {f : (ConfigSpace E) →ᵇ ℝ}
-- given
  (h : WeakConvergesTo μ ν) :
-- imply
  Tendsto (fun n => ∫ x, f x ∂(μ n : Measure (ConfigSpace E))) atTop (𝓝 (∫ x, f x ∂(ν : Measure (ConfigSpace E)))) := by
-- proof
  apply StatMech.WeakConvergesTo.tendsto_integral h f

/--
[weakConvergesTo_of_forall_tendsto_integral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/WeakConvergence.lean)
-/
@[path]
private lemma weakConvergesTo_of_forall_tendsto_integral_eq
  [Countable E]
  {μ : ℕ → ProbabilityMeasure (ConfigSpace E)}
  {ν : ProbabilityMeasure (ConfigSpace E)}
-- given
  (h : ∀ f : (ConfigSpace E) →ᵇ ℝ, Tendsto (fun n => ∫ x, f x ∂(μ n : Measure (ConfigSpace E))) atTop (𝓝 (∫ x, f x ∂(ν : Measure (ConfigSpace E))))) :
-- imply
  WeakConvergesTo μ ν := by
-- proof
  apply StatMech.weakConvergesTo_of_forall_tendsto_integral h


-- created on 2026-10-23
