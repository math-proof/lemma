import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneFactorCheckProduct
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[generatedClearedSkewPoly_eq_factors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneFactorCheckProduct.lean)
-/
@[path]
private lemma generatedClearedSkewPoly_eq_factors_eq :
-- imply
  generatedClearedSkewPoly = generatedQuotientPoly * BiPoly.xSquareSubOne * BiPoly.ySquareSubOne := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.generatedClearedSkewPoly_eq_factors


-- created on 2026-10-23
