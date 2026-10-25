import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexGapEtaModular
open Filter Topology Complex UpperHalfPlane StatMech StatMech.FrontierD


/--
[eta_imaginary_pow_twentyFour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexGapEtaModular.lean)
-/
@[path]
private lemma eta_imaginary_pow_twentyFour_eq
  {t : ℝ}
-- given
  (ht : 0 < t) :
-- imply
  ModularForm.eta (Complex.I * t) ^ 24 = (Real.exp (24 * (sixVertexEulerLog t - Real.pi * t / 12)) : ℝ) := by
-- proof
  apply StatMech.FrontierD.eta_imaginary_pow_twentyFour ht

/--
[eta_imaginary_recip_pow_twentyFour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexGapEtaModular.lean)
-/
@[path]
private lemma eta_imaginary_recip_pow_twentyFour_eq
  {t : ℝ}
-- given
  (ht : 0 < t) :
-- imply
  ModularForm.eta (Complex.I * (1 / t : ℝ)) ^ 24 = (t : ℂ) ^ 12 * ModularForm.eta (Complex.I * t) ^ 24 := by
-- proof
  apply StatMech.FrontierD.eta_imaginary_recip_pow_twentyFour ht

/--
[sixVertexEulerLog_reciprocal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexGapEtaModular.lean)
-/
@[path]
private lemma sixVertexEulerLog_reciprocal_eq
  {t : ℝ}
-- given
  (ht : 0 < t) :
-- imply
  sixVertexEulerLog (1 / t) = sixVertexEulerLog t + Real.log t / 2 + Real.pi / 12 * (1 / t - t) := by
-- proof
  apply StatMech.FrontierD.sixVertexEulerLog_reciprocal ht

/--
[sixVertexOddEulerRatioLog_reciprocal_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexGapEtaModular.lean)
-/
@[path]
private lemma sixVertexOddEulerRatioLog_reciprocal_four_eq
  {t : ℝ}
-- given
  (ht : 0 < t) :
-- imply
  sixVertexOddEulerRatioLog (1 / (4 * t)) = sixVertexAlternatingPlusEulerLog t + Real.pi * t / 4 - Real.log 2 / 2 := by
-- proof
  apply StatMech.FrontierD.sixVertexOddEulerRatioLog_reciprocal_four ht

/--
[sixVertexAntiferroelectricGapRate_eq_dualGapRate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexGapEtaModular.lean)
-/
@[path]
private lemma sixVertexAntiferroelectricGapRate_eq_dualGapRate_eq
  {lam : ℝ}
-- given
  (hlam : 0 < lam) :
-- imply
  sixVertexAntiferroelectricGapRate lam = sixVertexDualGapRate lam := by
-- proof
  apply StatMech.FrontierD.sixVertexAntiferroelectricGapRate_eq_dualGapRate hlam


-- created on 2026-10-23
