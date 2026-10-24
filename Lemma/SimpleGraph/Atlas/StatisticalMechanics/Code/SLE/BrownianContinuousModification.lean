import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.SLE.BrownianContinuousModification
open Filter MeasureTheory ProbabilityTheory Set StatMech StatMech.SLE


/--
[brownianDyadicApproxIndex_eq_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianContinuousModification.lean)
-/
@[path]
private lemma brownianDyadicApproxIndex_eq_add_eq
  {N L n : Nat}
  {t : Real}
-- given
  (hNL : N <= L)
  (htLower : -(N : Real) <= t) :
-- imply
  brownianDyadicApproxIndex L n t = brownianDyadicApproxIndex N n t + (L - N) * brownianDyadicDenominator n := by
-- proof
  apply StatMech.SLE.brownianDyadicApproxIndex_eq_add N L n hNL htLower

/--
[brownianDyadicApproxPoint_eq_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianContinuousModification.lean)
-/
@[path]
private lemma brownianDyadicApproxPoint_eq_of_le_eq
  {N L n : Nat}
  {t : Real}
-- given
  (hNL : N <= L)
  (htLower : -(N : Real) <= t) :
-- imply
  brownianDyadicApproxPoint L n t = brownianDyadicApproxPoint N n t := by
-- proof
  apply StatMech.SLE.brownianDyadicApproxPoint_eq_of_le N L n hNL htLower

/--
[brownianDyadicLimit_eq_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianContinuousModification.lean)
-/
@[path]
private lemma brownianDyadicLimit_eq_of_le_eq
  {N L : Nat}
  {t : Real}
-- given
  (omega : Real -> Real)
  (hNL : N <= L)
  (htLower : -(N : Real) <= t) :
-- imply
  brownianDyadicLimit L t omega = brownianDyadicLimit N t omega := by
-- proof
  apply StatMech.SLE.brownianDyadicLimit_eq_of_le omega N L hNL htLower

/--
[neg_brownianCompactRadius_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianContinuousModification.lean)
-/
@[path]
private lemma neg_brownianCompactRadius_le_eq
  {t : Real} :
-- imply
  -(brownianCompactRadius t : Real) <= t := by
-- proof
  apply StatMech.SLE.neg_brownianCompactRadius_le t

/--
[le_brownianCompactRadius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianContinuousModification.lean)
-/
@[path]
private lemma le_brownianCompactRadius_eq
  {t : Real} :
-- imply
  t <= brownianCompactRadius t := by
-- proof
  apply StatMech.SLE.le_brownianCompactRadius t

/--
[brownianContinuousModification_eq_dyadicLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianContinuousModification.lean)
-/
@[path]
private lemma brownianContinuousModification_eq_dyadicLimit_eq
  {N : Nat}
  {t : Real}
-- given
  (omega : Real -> Real)
  (htLower : -(N : Real) <= t)
  (htUpper : t <= N) :
-- imply
  brownianContinuousModification t omega = brownianDyadicLimit N t omega := by
-- proof
  apply StatMech.SLE.brownianContinuousModification_eq_dyadicLimit omega N htLower htUpper

/--
[continuous_brownianContinuousModification](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianContinuousModification.lean)
-/
@[path]
private lemma continuous_brownianContinuousModification_eq
-- given
  (omega : Real -> Real)
  (hgood : ∀ N : Nat, ∀ᶠ n in atTop, ∀ k ∈ Finset.range (2 * N * brownianDyadicDenominator n), edist (brownianCoordinateProcess (brownianDyadicPoint N n k) omega) (brownianCoordinateProcess (brownianDyadicPoint N n (k + 1)) omega) < brownianDyadicThreshold n) :
-- imply
  Continuous (fun t => brownianContinuousModification t omega) := by
-- proof
  apply StatMech.SLE.continuous_brownianContinuousModification omega hgood


-- created on 2026-10-23
