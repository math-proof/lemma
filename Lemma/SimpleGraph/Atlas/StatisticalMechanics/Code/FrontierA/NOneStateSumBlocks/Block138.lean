import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block138
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock138_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block138.lean)
-/
@[path]
private lemma directStateBlock138_checked_eq :
-- imply
  rawMomentDirectBlock 276 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock138 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock138_checked


-- created on 2026-10-23
