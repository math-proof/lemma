import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.SLE.BrownianProductProcess
open MeasureTheory ProbabilityTheory StatMech StatMech.SLE


/--
[brownianCoordinateProcess_measurable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianProductProcess.lean)
-/
@[path]
private lemma brownianCoordinateProcess_measurable_eq
  {t : Real} :
-- imply
  Measurable (brownianCoordinateProcess t) := by
-- proof
  apply StatMech.SLE.brownianCoordinateProcess_measurable t

/--
[brownianCoordinateProcess_isGaussianProcess](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianProductProcess.lean)
-/
@[path]
private lemma brownianCoordinateProcess_isGaussianProcess_eq :
-- imply
  IsGaussianProcess brownianCoordinateProcess brownianProductLaw where hasGaussianLaw I := by
-- proof
  apply StatMech.SLE.brownianCoordinateProcess_isGaussianProcess

/--
[brownianFiniteDimensionalPiLaw_measurePreserving_increment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianProductProcess.lean)
-/
@[path]
private lemma brownianFiniteDimensionalPiLaw_measurePreserving_increment_eq
  {I : Finset Real}
  {s t : I} :
-- imply
  MeasurePreserving (fun x : I -> Real => x t - x s) (brownianFiniteDimensionalPiLaw I) (gaussianReal 0 |(t : Real) - (s : Real)|.toNNReal) where measurable := by
-- proof
  apply StatMech.SLE.brownianFiniteDimensionalPiLaw_measurePreserving_increment I s t

/--
[brownianFiniteDimensionalPiLaw_measurePreserving_eval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianProductProcess.lean)
-/
@[path]
private lemma brownianFiniteDimensionalPiLaw_measurePreserving_eval_eq
  {I : Finset Real}
  {t : I} :
-- imply
  MeasurePreserving (fun x : I -> Real => x t) (brownianFiniteDimensionalPiLaw I) (gaussianReal 0 |(t : Real)|.toNNReal) where measurable := by
-- proof
  apply StatMech.SLE.brownianFiniteDimensionalPiLaw_measurePreserving_eval I t

/--
[brownianCoordinateProcess_eval_law](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianProductProcess.lean)
-/
@[path]
private lemma brownianCoordinateProcess_eval_law_eq
  {t : Real} :
-- imply
  HasLaw (brownianCoordinateProcess t) (gaussianReal 0 |t|.toNNReal) brownianProductLaw := by
-- proof
  apply StatMech.SLE.brownianCoordinateProcess_eval_law t

/--
[brownianCoordinateProcess_start](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianProductProcess.lean)
-/
@[path]
private lemma brownianCoordinateProcess_start_eq :
-- imply
  ∀ᵐ omega ∂brownianProductLaw, brownianCoordinateProcess 0 omega = 0 := by
-- proof
  apply StatMech.SLE.brownianCoordinateProcess_start

/--
[brownianFiniteDimensionalPiLaw_indepFun_increments](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianProductProcess.lean)
-/
@[path]
private lemma brownianFiniteDimensionalPiLaw_indepFun_increments_eq
  {I : Finset Real}
  {s t u v : I}
-- given
  (hst : (s : Real) <= t)
  (htu : (t : Real) <= u)
  (huv : (u : Real) <= v) :
-- imply
  IndepFun (fun x : I -> Real => x t - x s) (fun x : I -> Real => x v - x u) (brownianFiniteDimensionalPiLaw I) := by
-- proof
  apply StatMech.SLE.brownianFiniteDimensionalPiLaw_indepFun_increments I s t u v hst htu huv

/--
[brownianCoordinateProcess_indep_increments](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianProductProcess.lean)
-/
@[path]
private lemma brownianCoordinateProcess_indep_increments_eq
  {s t u v : Real}
-- given
  (hst : s <= t)
  (htu : t <= u)
  (huv : u <= v) :
-- imply
  IndepFun (fun omega => brownianCoordinateProcess t omega - brownianCoordinateProcess s omega) (fun omega => brownianCoordinateProcess v omega - brownianCoordinateProcess u omega) brownianProductLaw := by
-- proof
  apply StatMech.SLE.brownianCoordinateProcess_indep_increments s t u v hst htu huv

/--
[brownianCoordinateProcess_increment_law](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianProductProcess.lean)
-/
@[path]
private lemma brownianCoordinateProcess_increment_law_eq
  {s t : Real} :
-- imply
  HasLaw (fun omega => brownianCoordinateProcess t omega - brownianCoordinateProcess s omega) (gaussianReal 0 |t - s|.toNNReal) brownianProductLaw := by
-- proof
  apply StatMech.SLE.brownianCoordinateProcess_increment_law s t

/--
[integral_norm_increment_pow_four_brownianProductLaw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianProductProcess.lean)
-/
@[path]
private lemma integral_norm_increment_pow_four_brownianProductLaw_eq
  {s t : Real} :
-- imply
  integral brownianProductLaw (fun omega => norm (brownianCoordinateProcess t omega - brownianCoordinateProcess s omega) ^ 4) = 3 * := by
-- proof
  apply StatMech.SLE.integral_norm_increment_pow_four_brownianProductLaw s t

/--
[brownianCoordinateProcess_isKolmogorovProcess](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianProductProcess.lean)
-/
@[path]
private lemma brownianCoordinateProcess_isKolmogorovProcess_eq :
-- imply
  IsKolmogorovProcess brownianCoordinateProcess brownianProductLaw 4 2 3 := by
-- proof
  apply StatMech.SLE.brownianCoordinateProcess_isKolmogorovProcess


-- created on 2026-10-23
