import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block109
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock109_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block109.lean)
-/
@[path]
private lemma directStateBlock109_checked_eq :
-- imply
  rawMomentDirectBlock 218 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock109 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock109_checked


-- created on 2026-10-23
