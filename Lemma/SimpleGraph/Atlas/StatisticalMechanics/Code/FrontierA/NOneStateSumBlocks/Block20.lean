import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block20
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock20_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block20.lean)
-/
@[path]
private lemma directStateBlock20_checked_eq :
-- imply
  rawMomentDirectBlock 40 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock20 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock20_checked


-- created on 2026-10-23
