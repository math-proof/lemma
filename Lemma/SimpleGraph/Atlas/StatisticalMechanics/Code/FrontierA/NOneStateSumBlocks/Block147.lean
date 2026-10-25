import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block147
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock147_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block147.lean)
-/
@[path]
private lemma directStateBlock147_checked_eq :
-- imply
  rawMomentDirectBlock 294 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock147 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock147_checked


-- created on 2026-10-23
