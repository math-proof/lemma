import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block210
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock210_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block210.lean)
-/
@[path]
private lemma directStateBlock210_checked_eq :
-- imply
  rawMomentDirectBlock 420 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock210 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock210_checked


-- created on 2026-10-23
