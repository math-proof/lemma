import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block140
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock140_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block140.lean)
-/
@[path]
private lemma directStateBlock140_checked_eq :
-- imply
  rawMomentDirectBlock 280 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock140 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock140_checked


-- created on 2026-10-23
