import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block76
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock76_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block76.lean)
-/
@[path]
private lemma directStateBlock76_checked_eq :
-- imply
  rawMomentDirectBlock 152 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock76 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock76_checked


-- created on 2026-10-23
