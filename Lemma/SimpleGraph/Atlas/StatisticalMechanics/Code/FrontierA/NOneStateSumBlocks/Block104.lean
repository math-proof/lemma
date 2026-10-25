import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block104
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock104_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block104.lean)
-/
@[path]
private lemma directStateBlock104_checked_eq :
-- imply
  rawMomentDirectBlock 208 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock104 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock104_checked


-- created on 2026-10-23
