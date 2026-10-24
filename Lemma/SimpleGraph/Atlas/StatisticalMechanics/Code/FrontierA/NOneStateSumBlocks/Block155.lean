import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block155
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock155_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block155.lean)
-/
@[path]
private lemma directStateBlock155_checked_eq :
-- imply
  rawMomentDirectBlock 310 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock155 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock155_checked


-- created on 2026-10-23
