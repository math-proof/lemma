import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block108
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock108_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block108.lean)
-/
@[path]
private lemma directStateBlock108_checked_eq :
-- imply
  rawMomentDirectBlock 216 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock108 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock108_checked


-- created on 2026-10-23
