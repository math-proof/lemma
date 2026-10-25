import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block239
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock239_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block239.lean)
-/
@[path]
private lemma directStateBlock239_checked_eq :
-- imply
  rawMomentDirectBlock 478 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock239 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock239_checked


-- created on 2026-10-23
