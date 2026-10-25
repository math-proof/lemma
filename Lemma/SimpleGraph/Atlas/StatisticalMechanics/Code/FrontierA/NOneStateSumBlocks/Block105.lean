import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block105
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock105_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block105.lean)
-/
@[path]
private lemma directStateBlock105_checked_eq :
-- imply
  rawMomentDirectBlock 210 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock105 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock105_checked


-- created on 2026-10-23
