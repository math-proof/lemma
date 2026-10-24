import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block98
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock98_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block98.lean)
-/
@[path]
private lemma directStateBlock98_checked_eq :
-- imply
  rawMomentDirectBlock 196 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock98 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock98_checked


-- created on 2026-10-23
