import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block245
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock245_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block245.lean)
-/
@[path]
private lemma directStateBlock245_checked_eq :
-- imply
  rawMomentDirectBlock 490 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock245 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock245_checked


-- created on 2026-10-23
