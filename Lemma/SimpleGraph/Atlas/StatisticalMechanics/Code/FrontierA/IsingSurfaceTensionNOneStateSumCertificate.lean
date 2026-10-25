import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneStateSumCertificate
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[rawMomentPolyStateSum_eq_generatedDirectStateSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneStateSumCertificate.lean)
-/
@[path]
private lemma rawMomentPolyStateSum_eq_generatedDirectStateSum_eq :
-- imply
  rawMomentPolyStateSum = generatedDirectStateSum := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.rawMomentPolyStateSum_eq_generatedDirectStateSum

/--
[generatedDirectStateSum_eq_generatedRawMomentPoly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneStateSumCertificate.lean)
-/
@[path]
private lemma generatedDirectStateSum_eq_generatedRawMomentPoly_eq :
-- imply
  generatedDirectStateSum = generatedRawMomentPoly := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.generatedDirectStateSum_eq_generatedRawMomentPoly

/--
[rawMomentPolyStateSum_eq_rawMomentPoly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneStateSumCertificate.lean)
-/
@[path]
private lemma rawMomentPolyStateSum_eq_rawMomentPoly_eq :
-- imply
  rawMomentPolyStateSum = rawMomentPoly := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.rawMomentPolyStateSum_eq_rawMomentPoly

/--
[eval_rawMomentPolyStateSum_eq_rawMomentPoly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneStateSumCertificate.lean)
-/
@[path]
private lemma eval_rawMomentPolyStateSum_eq_rawMomentPoly_eq
  {X Y : Real} :
-- imply
  rawMomentPolyStateSum.eval X Y = rawMomentPoly.eval X Y := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.eval_rawMomentPolyStateSum_eq_rawMomentPoly X Y


-- created on 2026-10-23
