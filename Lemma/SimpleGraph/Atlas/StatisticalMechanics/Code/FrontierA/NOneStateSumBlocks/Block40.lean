import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block40
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock40_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block40.lean)
-/
@[path]
private lemma directStateBlock40_checked_eq :
-- imply
  rawMomentDirectBlock 80 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock40 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock40_checked


-- created on 2026-10-23
