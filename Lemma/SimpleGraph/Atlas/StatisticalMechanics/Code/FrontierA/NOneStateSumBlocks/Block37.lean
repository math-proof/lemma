import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block37
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock37_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block37.lean)
-/
@[path]
private lemma directStateBlock37_checked_eq :
-- imply
  rawMomentDirectBlock 74 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock37 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock37_checked


-- created on 2026-10-23
