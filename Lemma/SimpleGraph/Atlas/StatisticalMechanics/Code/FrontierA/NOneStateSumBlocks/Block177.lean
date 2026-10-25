import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block177
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock177_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block177.lean)
-/
@[path]
private lemma directStateBlock177_checked_eq :
-- imply
  rawMomentDirectBlock 354 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock177 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock177_checked


-- created on 2026-10-23
