import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneFactorCheckCleared
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[clearedSkewPoly_eq_generated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneFactorCheckCleared.lean)
-/
@[path]
private lemma clearedSkewPoly_eq_generated_eq :
-- imply
  clearedSkewPoly = generatedClearedSkewPoly := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.clearedSkewPoly_eq_generated


-- created on 2026-10-23
