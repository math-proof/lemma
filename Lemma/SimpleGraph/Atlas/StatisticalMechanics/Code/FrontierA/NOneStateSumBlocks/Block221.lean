import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block221
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock221_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block221.lean)
-/
@[path]
private lemma directStateBlock221_checked_eq :
-- imply
  rawMomentDirectBlock 442 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock221 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock221_checked


-- created on 2026-10-23
