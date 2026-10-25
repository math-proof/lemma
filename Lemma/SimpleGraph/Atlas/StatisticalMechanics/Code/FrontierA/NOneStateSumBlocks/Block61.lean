import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block61
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock61_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block61.lean)
-/
@[path]
private lemma directStateBlock61_checked_eq :
-- imply
  rawMomentDirectBlock 122 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock61 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock61_checked


-- created on 2026-10-23
