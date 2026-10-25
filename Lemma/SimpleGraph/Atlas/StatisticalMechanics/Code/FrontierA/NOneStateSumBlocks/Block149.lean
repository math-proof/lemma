import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block149
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock149_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block149.lean)
-/
@[path]
private lemma directStateBlock149_checked_eq :
-- imply
  rawMomentDirectBlock 298 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock149 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock149_checked


-- created on 2026-10-23
