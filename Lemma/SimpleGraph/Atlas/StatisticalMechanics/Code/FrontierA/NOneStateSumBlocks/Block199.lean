import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block199
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock199_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block199.lean)
-/
@[path]
private lemma directStateBlock199_checked_eq :
-- imply
  rawMomentDirectBlock 398 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock199 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock199_checked


-- created on 2026-10-23
