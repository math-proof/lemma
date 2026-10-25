import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block127
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock127_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block127.lean)
-/
@[path]
private lemma directStateBlock127_checked_eq :
-- imply
  rawMomentDirectBlock 254 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock127 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock127_checked


-- created on 2026-10-23
