import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block135
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock135_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block135.lean)
-/
@[path]
private lemma directStateBlock135_checked_eq :
-- imply
  rawMomentDirectBlock 270 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock135 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock135_checked


-- created on 2026-10-23
