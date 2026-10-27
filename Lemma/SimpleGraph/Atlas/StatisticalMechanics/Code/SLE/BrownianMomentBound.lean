import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.SLE.BrownianMomentBound
open MeasureTheory ProbabilityTheory StatMech StatMech.SLE


/--
[integral_pow_four_gaussianReal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianMomentBound.lean)
-/
@[path]
private lemma integral_pow_four_gaussianReal_eq
  {v : NNReal} :
-- imply
  ∫ x : ℝ, x ^ 4 ∂(gaussianReal 0 v) = 3 * (v : ℝ) ^ 2 := by
-- proof
  apply StatMech.SLE.integral_pow_four_gaussianReal v

/--
[integral_increment_pow_four_brownianFiniteDimensionalLaw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianMomentBound.lean)
-/
@[path]
private lemma integral_increment_pow_four_brownianFiniteDimensionalLaw_eq
  {I : Finset ℝ}
  {s t : I} :
-- imply
  ∫ x : EuclideanSpace ℝ I, (x t - x s) ^ 4 ∂(brownianFiniteDimensionalLaw I) = 3 * := by
-- proof
  apply StatMech.SLE.integral_increment_pow_four_brownianFiniteDimensionalLaw I s t

/--
[integral_norm_increment_pow_four_brownianFiniteDimensionalLaw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianMomentBound.lean)
-/
@[path]
private lemma integral_norm_increment_pow_four_brownianFiniteDimensionalLaw_eq
  {I : Finset ℝ}
  {s t : I} :
-- imply
  ∫ x : EuclideanSpace ℝ I, ‖x t - x s‖ ^ 4 ∂(brownianFiniteDimensionalLaw I) = 3 * := by
-- proof
  apply StatMech.SLE.integral_norm_increment_pow_four_brownianFiniteDimensionalLaw I s t

/--
[brownianFiniteDimensionalLaw_isKolmogorovProcess](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianMomentBound.lean)
-/
@[path]
private lemma brownianFiniteDimensionalLaw_isKolmogorovProcess_eq
  {I : Finset ℝ} :
-- imply
  IsKolmogorovProcess (fun t : I ↦ fun x : EuclideanSpace ℝ I ↦ x t) (brownianFiniteDimensionalLaw I) 4 2 3 := by
-- proof
  apply StatMech.SLE.brownianFiniteDimensionalLaw_isKolmogorovProcess I

/--
[integral_norm_increment_pow_four_brownianFiniteDimensionalPiLaw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianMomentBound.lean)
-/
@[path]
private lemma integral_norm_increment_pow_four_brownianFiniteDimensionalPiLaw_eq
  {I : Finset ℝ}
  {s t : I} :
-- imply
  ∫ x : I → ℝ, ‖x t - x s‖ ^ 4 ∂(brownianFiniteDimensionalPiLaw I) = 3 * := by
-- proof
  apply StatMech.SLE.integral_norm_increment_pow_four_brownianFiniteDimensionalPiLaw I s t

/--
[brownianFiniteDimensionalPiLaw_isKolmogorovProcess](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianMomentBound.lean)
-/
@[path]
private lemma brownianFiniteDimensionalPiLaw_isKolmogorovProcess_eq
  {I : Finset ℝ} :
-- imply
  IsKolmogorovProcess (fun t : I ↦ fun x : I → ℝ ↦ x t) (brownianFiniteDimensionalPiLaw I) 4 2 3 := by
-- proof
  apply StatMech.SLE.brownianFiniteDimensionalPiLaw_isKolmogorovProcess I


-- created on 2026-10-23
