import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block180
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock180_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block180.lean)
-/
@[path]
private lemma directStateBlock180_checked_eq :
-- imply
  rawMomentDirectBlock 360 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock180 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock180_checked


-- created on 2026-10-23
