import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block192
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock192_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block192.lean)
-/
@[path]
private lemma directStateBlock192_checked_eq :
-- imply
  rawMomentDirectBlock 384 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock192 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock192_checked


-- created on 2026-10-23
