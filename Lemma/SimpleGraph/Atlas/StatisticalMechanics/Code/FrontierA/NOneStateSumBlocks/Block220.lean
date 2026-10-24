import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block220
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock220_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block220.lean)
-/
@[path]
private lemma directStateBlock220_checked_eq :
-- imply
  rawMomentDirectBlock 440 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock220 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock220_checked


-- created on 2026-10-23
