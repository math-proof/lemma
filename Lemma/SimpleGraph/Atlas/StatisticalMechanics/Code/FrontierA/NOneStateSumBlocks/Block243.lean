import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block243
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock243_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block243.lean)
-/
@[path]
private lemma directStateBlock243_checked_eq :
-- imply
  rawMomentDirectBlock 486 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock243 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock243_checked


-- created on 2026-10-23
