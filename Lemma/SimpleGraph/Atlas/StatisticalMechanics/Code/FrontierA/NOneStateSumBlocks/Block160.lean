import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block160
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock160_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block160.lean)
-/
@[path]
private lemma directStateBlock160_checked_eq :
-- imply
  rawMomentDirectBlock 320 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock160 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock160_checked


-- created on 2026-10-23
