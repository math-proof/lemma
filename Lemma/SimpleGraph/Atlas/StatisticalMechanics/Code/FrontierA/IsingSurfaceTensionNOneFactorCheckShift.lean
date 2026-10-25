import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneFactorCheckShift
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[generatedQuotientPoly_shiftToOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneFactorCheckShift.lean)
-/
@[path]
private lemma generatedQuotientPoly_shiftToOne_eq :
-- imply
  generatedQuotientPoly.shiftToOne = generatedShiftedQuotientPoly := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.generatedQuotientPoly_shiftToOne

/--
[generatedQuotientPoly_exponents_nonnegative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneFactorCheckShift.lean)
-/
@[path]
private lemma generatedQuotientPoly_exponents_nonnegative_eq :
-- imply
  ∀ t ∈ generatedQuotientPoly.terms, 0 ≤ t.ex ∧ 0 ≤ t.ey := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.generatedQuotientPoly_exponents_nonnegative

/--
[generatedShiftedQuotientPoly_coefficients_nonnegative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneFactorCheckShift.lean)
-/
@[path]
private lemma generatedShiftedQuotientPoly_coefficients_nonnegative_eq :
-- imply
  ∀ t ∈ generatedShiftedQuotientPoly.terms, 0 ≤ t.coeff := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.generatedShiftedQuotientPoly_coefficients_nonnegative


-- created on 2026-10-23
