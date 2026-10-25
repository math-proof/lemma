import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block238
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock238_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block238.lean)
-/
@[path]
private lemma directStateBlock238_checked_eq :
-- imply
  rawMomentDirectBlock 476 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock238 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock238_checked


-- created on 2026-10-23
