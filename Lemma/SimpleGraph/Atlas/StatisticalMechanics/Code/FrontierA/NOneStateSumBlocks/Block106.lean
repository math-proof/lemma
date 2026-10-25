import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block106
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock106_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block106.lean)
-/
@[path]
private lemma directStateBlock106_checked_eq :
-- imply
  rawMomentDirectBlock 212 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock106 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock106_checked


-- created on 2026-10-23
