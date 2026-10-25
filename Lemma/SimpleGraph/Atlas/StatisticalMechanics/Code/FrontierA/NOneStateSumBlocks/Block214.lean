import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block214
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock214_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block214.lean)
-/
@[path]
private lemma directStateBlock214_checked_eq :
-- imply
  rawMomentDirectBlock 428 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock214 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock214_checked


-- created on 2026-10-23
