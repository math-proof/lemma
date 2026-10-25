import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block04
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock4_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block04.lean)
-/
@[path]
private lemma directStateBlock4_checked_eq :
-- imply
  rawMomentDirectBlock 8 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock4 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock4_checked


-- created on 2026-10-23
