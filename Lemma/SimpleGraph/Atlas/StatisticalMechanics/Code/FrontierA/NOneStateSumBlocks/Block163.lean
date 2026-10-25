import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block163
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock163_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block163.lean)
-/
@[path]
private lemma directStateBlock163_checked_eq :
-- imply
  rawMomentDirectBlock 326 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock163 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock163_checked


-- created on 2026-10-23
