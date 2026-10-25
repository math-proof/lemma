import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block129
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock129_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block129.lean)
-/
@[path]
private lemma directStateBlock129_checked_eq :
-- imply
  rawMomentDirectBlock 258 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock129 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock129_checked


-- created on 2026-10-23
