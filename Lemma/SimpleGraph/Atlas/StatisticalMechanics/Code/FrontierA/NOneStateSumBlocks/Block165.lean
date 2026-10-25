import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block165
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock165_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block165.lean)
-/
@[path]
private lemma directStateBlock165_checked_eq :
-- imply
  rawMomentDirectBlock 330 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock165 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock165_checked


-- created on 2026-10-23
