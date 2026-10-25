import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.SLE.BrownianFiniteDimensional.Part4
open MeasureTheory Matrix ProbabilityTheory Set WithLp StatMech StatMech.SLE


/--
[brownianCovariance_eq_volumeReal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianFiniteDimensional.lean)
-/
@[path]
private lemma brownianCovariance_eq_volumeReal_eq
  {s t : ℝ} :
-- imply
  brownianCovariance s t = (volume : Measure ℝ).real (uIoc 0 s ∩ uIoc 0 t) := by
-- proof
  apply StatMech.SLE.brownianCovariance_eq_volumeReal s t

/--
[brownianCovariance_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianFiniteDimensional.lean)
-/
@[path]
private lemma brownianCovariance_eq_eq
  {s t : ℝ} :
-- imply
  brownianCovariance s t = (|s| + |t| - |t - s|) / 2 := by
-- proof
  apply StatMech.SLE.brownianCovariance_eq s t

/--
[brownianCovariance_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianFiniteDimensional.lean)
-/
@[path]
private lemma brownianCovariance_self_eq
  {t : ℝ} :
-- imply
  brownianCovariance t t = := by
-- proof
  apply StatMech.SLE.brownianCovariance_self t

/--
[brownianCovariance_zero_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianFiniteDimensional.lean)
-/
@[path]
private lemma brownianCovariance_zero_left_eq
  {t : ℝ} :
-- imply
  brownianCovariance 0 t = 0 := by
-- proof
  apply StatMech.SLE.brownianCovariance_zero_left t

/--
[brownianCovariance_zero_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianFiniteDimensional.lean)
-/
@[path]
private lemma brownianCovariance_zero_right_eq
  {t : ℝ} :
-- imply
  brownianCovariance t 0 = 0 := by
-- proof
  apply StatMech.SLE.brownianCovariance_zero_right t

/--
[brownianCovariance_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianFiniteDimensional.lean)
-/
@[path]
private lemma brownianCovariance_symm_eq
  {s t : ℝ} :
-- imply
  brownianCovariance s t = brownianCovariance t s := by
-- proof
  apply StatMech.SLE.brownianCovariance_symm s t

/--
[brownianCovarianceMatrix_eq_gram](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianFiniteDimensional.lean)
-/
@[path]
private lemma brownianCovarianceMatrix_eq_gram_eq
  {I : Finset ℝ} :
-- imply
  brownianCovarianceMatrix I = gram ℝ (fun t : I => brownianCovVector t) := by
-- proof
  apply StatMech.SLE.brownianCovarianceMatrix_eq_gram I

/--
[brownianCovarianceMatrix_posSemidef](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianFiniteDimensional.lean)
-/
@[path]
private lemma brownianCovarianceMatrix_posSemidef_eq
  {I : Finset ℝ} :
-- imply
  (brownianCovarianceMatrix I).PosSemidef := by
-- proof
  apply StatMech.SLE.brownianCovarianceMatrix_posSemidef I

/--
[memLp_eval_brownianFiniteDimensionalLaw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianFiniteDimensional.lean)
-/
@[path]
private lemma memLp_eval_brownianFiniteDimensionalLaw_eq
  {I : Finset ℝ}
  {t : I} :
-- imply
  MemLp (fun x : EuclideanSpace ℝ I => x t) 2 (brownianFiniteDimensionalLaw I) := by
-- proof
  apply StatMech.SLE.memLp_eval_brownianFiniteDimensionalLaw I t

/--
[brownianFiniteDimensionalLaw_measurePreserving_eval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianFiniteDimensional.lean)
-/
@[path]
private lemma brownianFiniteDimensionalLaw_measurePreserving_eval_eq
  {I : Finset ℝ}
  {t : I} :
-- imply
  MeasurePreserving (fun x : EuclideanSpace ℝ I => x t) (brownianFiniteDimensionalLaw I) (ProbabilityTheory.gaussianReal 0 |(t : ℝ)|.toNNReal) := by
-- proof
  apply StatMech.SLE.brownianFiniteDimensionalLaw_measurePreserving_eval I t

/--
[integral_increment_brownianFiniteDimensionalLaw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianFiniteDimensional.lean)
-/
@[path]
private lemma integral_increment_brownianFiniteDimensionalLaw_eq
  {I : Finset ℝ}
  {s t : I} :
-- imply
  ∫ x, (x t - x s) ∂(brownianFiniteDimensionalLaw I) = 0 := by
-- proof
  apply StatMech.SLE.integral_increment_brownianFiniteDimensionalLaw I s t

/--
[variance_increment_brownianFiniteDimensionalLaw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianFiniteDimensional.lean)
-/
@[path]
private lemma variance_increment_brownianFiniteDimensionalLaw_eq
  {I : Finset ℝ}
  {s t : I} :
-- imply
  Var[(fun x : EuclideanSpace ℝ I => x t - x s); brownianFiniteDimensionalLaw I] = := by
-- proof
  apply StatMech.SLE.variance_increment_brownianFiniteDimensionalLaw I s t

/--
[brownianFiniteDimensionalLaw_measurePreserving_increment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianFiniteDimensional.lean)
-/
@[path]
private lemma brownianFiniteDimensionalLaw_measurePreserving_increment_eq
  {I : Finset ℝ}
  {s t : I} :
-- imply
  MeasurePreserving (fun x : EuclideanSpace ℝ I => x t - x s) (brownianFiniteDimensionalLaw I) (ProbabilityTheory.gaussianReal 0 |(t : ℝ) - (s : ℝ)|.toNNReal) where measurable := by
-- proof
  apply StatMech.SLE.brownianFiniteDimensionalLaw_measurePreserving_increment I s t

/--
[covariance_disjoint_increments_brownianFiniteDimensionalLaw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianFiniteDimensional.lean)
-/
@[path]
private lemma covariance_disjoint_increments_brownianFiniteDimensionalLaw_eq
  {I : Finset ℝ}
  {s t u v : I}
-- given
  (hst : (s : ℝ) ≤ t)
  (htu : (t : ℝ) ≤ u)
  (huv : (u : ℝ) ≤ v) :
-- imply
  cov[(fun x : EuclideanSpace ℝ I => x t - x s), (fun x : EuclideanSpace ℝ I => x v - x u); brownianFiniteDimensionalLaw I] = 0 := by
-- proof
  apply StatMech.SLE.covariance_disjoint_increments_brownianFiniteDimensionalLaw I s t u v hst htu huv

/--
[brownianFiniteDimensionalLaw_indepFun_increments](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianFiniteDimensional.lean)
-/
@[path]
private lemma brownianFiniteDimensionalLaw_indepFun_increments_eq
  {I : Finset ℝ}
  {s t u v : I}
-- given
  (hst : (s : ℝ) ≤ t)
  (htu : (t : ℝ) ≤ u)
  (huv : (u : ℝ) ≤ v) :
-- imply
  IndepFun (fun x : EuclideanSpace ℝ I => x t - x s) (fun x : EuclideanSpace ℝ I => x v - x u) (brownianFiniteDimensionalLaw I) := by
-- proof
  apply StatMech.SLE.brownianFiniteDimensionalLaw_indepFun_increments I s t u v hst htu huv

/--
[brownianFiniteDimensionalLaw_restrict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianFiniteDimensional.lean)
-/
@[path]
private lemma brownianFiniteDimensionalLaw_restrict_eq
  {I J : Finset ℝ}
-- given
  (hJI : J ⊆ I) :
-- imply
  MeasurePreserving (EuclideanSpace.restrict₂ hJI) (brownianFiniteDimensionalLaw I) (brownianFiniteDimensionalLaw J) := by
-- proof
  apply StatMech.SLE.brownianFiniteDimensionalLaw_restrict hJI

/--
[brownianFiniteDimensionalPiLaw_isProjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianFiniteDimensional.lean)
-/
@[path]
private lemma brownianFiniteDimensionalPiLaw_isProjective_eq :
-- imply
  @IsProjectiveMeasureFamily ℝ (fun _ => ℝ) (fun _ => inferInstance) brownianFiniteDimensionalPiLaw := by
-- proof
  apply StatMech.SLE.brownianFiniteDimensionalPiLaw_isProjective


-- created on 2026-10-23
