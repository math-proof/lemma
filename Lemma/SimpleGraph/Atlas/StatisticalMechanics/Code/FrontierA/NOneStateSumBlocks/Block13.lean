import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block13
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock13_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block13.lean)
-/
@[path]
private lemma directStateBlock13_checked_eq :
-- imply
  rawMomentDirectBlock 26 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock13 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock13_checked


-- created on 2026-10-23
