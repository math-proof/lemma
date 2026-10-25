import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block244
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock244_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block244.lean)
-/
@[path]
private lemma directStateBlock244_checked_eq :
-- imply
  rawMomentDirectBlock 488 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock244 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock244_checked


-- created on 2026-10-23
