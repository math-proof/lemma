import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block06
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock6_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block06.lean)
-/
@[path]
private lemma directStateBlock6_checked_eq :
-- imply
  rawMomentDirectBlock 12 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock6 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock6_checked


-- created on 2026-10-23
