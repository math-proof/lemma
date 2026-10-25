import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block184
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock184_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block184.lean)
-/
@[path]
private lemma directStateBlock184_checked_eq :
-- imply
  rawMomentDirectBlock 368 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock184 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock184_checked


-- created on 2026-10-23
