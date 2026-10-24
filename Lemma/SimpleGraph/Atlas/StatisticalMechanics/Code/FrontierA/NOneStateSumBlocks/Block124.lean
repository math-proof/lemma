import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block124
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock124_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block124.lean)
-/
@[path]
private lemma directStateBlock124_checked_eq :
-- imply
  rawMomentDirectBlock 248 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock124 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock124_checked


-- created on 2026-10-23
