import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block136
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock136_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block136.lean)
-/
@[path]
private lemma directStateBlock136_checked_eq :
-- imply
  rawMomentDirectBlock 272 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock136 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock136_checked


-- created on 2026-10-23
