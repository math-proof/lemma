import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOnePolynomialCertificate
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[generatedQuotientPoly_eval_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOnePolynomialCertificate.lean)
-/
@[path]
private lemma generatedQuotientPoly_eval_nonneg_eq
  {X Y : Real}
-- given
  (hX : 1 ≤ X)
  (hY : 1 ≤ Y) :
-- imply
  0 ≤ generatedQuotientPoly.eval X Y := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.generatedQuotientPoly_eval_nonneg X Y hX hY

/--
[clearedSkewPoly_eval_eq_generated_factors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOnePolynomialCertificate.lean)
-/
@[path]
private lemma clearedSkewPoly_eval_eq_generated_factors_eq
  {X Y : Real}
-- given
  (hX : X ≠ 0)
  (hY : Y ≠ 0) :
-- imply
  clearedSkewPoly.eval X Y = generatedQuotientPoly.eval X Y * (X ^ 2 - 1) * (Y ^ 2 - 1) := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.clearedSkewPoly_eval_eq_generated_factors X Y hX hY

/--
[reflectedVarianceSkewPoly_eval_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOnePolynomialCertificate.lean)
-/
@[path]
private lemma reflectedVarianceSkewPoly_eval_nonpos_eq
  {X Y : Real}
-- given
  (hX : 1 ≤ X)
  (hY : 1 ≤ Y) :
-- imply
  reflectedVarianceSkewPoly.eval X Y ≤ 0 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.reflectedVarianceSkewPoly_eval_nonpos X Y hX hY


-- created on 2026-10-23
