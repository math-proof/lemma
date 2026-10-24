import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block03
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock3_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block03.lean)
-/
@[path]
private lemma directStateBlock3_checked_eq :
-- imply
  rawMomentDirectBlock 6 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock3 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock3_checked


-- created on 2026-10-23
