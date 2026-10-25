import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block22
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock22_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block22.lean)
-/
@[path]
private lemma directStateBlock22_checked_eq :
-- imply
  rawMomentDirectBlock 44 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock22 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock22_checked


-- created on 2026-10-23
