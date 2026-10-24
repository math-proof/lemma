import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block70
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock70_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block70.lean)
-/
@[path]
private lemma directStateBlock70_checked_eq :
-- imply
  rawMomentDirectBlock 140 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock70 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock70_checked


-- created on 2026-10-23
