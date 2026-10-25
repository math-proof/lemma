import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.SLE.BrownianModificationLaw
open Filter MeasureTheory ProbabilityTheory Set StatMech StatMech.SLE


/--
[brownianCoordinateProcess_tendstoInMeasure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianModificationLaw.lean)
-/
@[path]
private lemma brownianCoordinateProcess_tendstoInMeasure_eq
  {s : Nat -> Real}
  {t : Real}
-- given
  (hs : Tendsto s atTop (nhds t)) :
-- imply
  TendstoInMeasure brownianProductLaw (fun n omega => brownianCoordinateProcess (s n) omega) atTop (brownianCoordinateProcess t) := by
-- proof
  apply StatMech.SLE.brownianCoordinateProcess_tendstoInMeasure hs

/--
[tendsto_brownianDyadicApproxPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianModificationLaw.lean)
-/
@[path]
private lemma tendsto_brownianDyadicApproxPoint_eq
  {N : Nat}
  {t : Real}
-- given
  (htLower : -(N : Real) <= t) :
-- imply
  Tendsto (fun n => brownianDyadicApproxPoint N n t) atTop (nhds t) := by
-- proof
  apply StatMech.SLE.tendsto_brownianDyadicApproxPoint N htLower

/--
[brownianContinuousModification_ae_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianModificationLaw.lean)
-/
@[path]
private lemma brownianContinuousModification_ae_eq_eq
  {t : Real} :
-- imply
  brownianContinuousModification t =ᵐ[brownianProductLaw] brownianCoordinateProcess t := by
-- proof
  apply StatMech.SLE.brownianContinuousModification_ae_eq t

/--
[brownianContinuousModification_measurable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianModificationLaw.lean)
-/
@[path]
private lemma brownianContinuousModification_measurable_eq
  {t : Real} :
-- imply
  Measurable (brownianContinuousModification t) := by
-- proof
  apply StatMech.SLE.brownianContinuousModification_measurable t

/--
[brownianContinuousModification_start](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianModificationLaw.lean)
-/
@[path]
private lemma brownianContinuousModification_start_eq :
-- imply
  ∀ᵐ omega ∂brownianProductLaw, brownianContinuousModification 0 omega = 0 := by
-- proof
  apply StatMech.SLE.brownianContinuousModification_start

/--
[brownianContinuousModification_continuous_paths](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianModificationLaw.lean)
-/
@[path]
private lemma brownianContinuousModification_continuous_paths_eq :
-- imply
  ∀ᵐ omega ∂brownianProductLaw, Continuous (fun t => brownianContinuousModification t omega) := by
-- proof
  apply StatMech.SLE.brownianContinuousModification_continuous_paths

/--
[brownianContinuousModification_isGaussianProcess](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianModificationLaw.lean)
-/
@[path]
private lemma brownianContinuousModification_isGaussianProcess_eq :
-- imply
  IsGaussianProcess brownianContinuousModification brownianProductLaw := by
-- proof
  apply StatMech.SLE.brownianContinuousModification_isGaussianProcess

/--
[brownianContinuousModification_increment_law](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianModificationLaw.lean)
-/
@[path]
private lemma brownianContinuousModification_increment_law_eq
  {s t : Real}
-- given
  (hst : s <= t) :
-- imply
  HasLaw (fun omega => brownianContinuousModification t omega - brownianContinuousModification s omega) (gaussianReal 0 (t - s).toNNReal) brownianProductLaw := by
-- proof
  apply StatMech.SLE.brownianContinuousModification_increment_law s t hst

/--
[brownianContinuousModification_indep_increments](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianModificationLaw.lean)
-/
@[path]
private lemma brownianContinuousModification_indep_increments_eq
  {s t u v : Real}
-- given
  (hst : s <= t)
  (htu : t <= u)
  (huv : u <= v) :
-- imply
  IndepFun (fun omega => brownianContinuousModification t omega - brownianContinuousModification s omega) (fun omega => brownianContinuousModification v omega - brownianContinuousModification u omega) brownianProductLaw := by
-- proof
  apply StatMech.SLE.brownianContinuousModification_indep_increments s t u v hst htu huv

/--
[brownianContinuousModification_isStandardBrownianMotion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianModificationLaw.lean)
-/
@[path]
private lemma brownianContinuousModification_isStandardBrownianMotion_eq :
-- imply
  IsStandardBrownianMotion brownianContinuousModification brownianProductLaw where start := by
-- proof
  apply StatMech.SLE.brownianContinuousModification_isStandardBrownianMotion


-- created on 2026-10-23
