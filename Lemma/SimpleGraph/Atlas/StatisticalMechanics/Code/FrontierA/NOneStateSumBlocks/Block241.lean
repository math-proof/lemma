import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block241
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock241_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block241.lean)
-/
@[path]
private lemma directStateBlock241_checked_eq :
-- imply
  rawMomentDirectBlock 482 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock241 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock241_checked


-- created on 2026-10-23
