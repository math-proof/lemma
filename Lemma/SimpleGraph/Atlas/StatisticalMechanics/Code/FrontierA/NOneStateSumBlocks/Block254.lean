import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block254
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock254_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block254.lean)
-/
@[path]
private lemma directStateBlock254_checked_eq :
-- imply
  rawMomentDirectBlock 508 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock254 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock254_checked


-- created on 2026-10-23
