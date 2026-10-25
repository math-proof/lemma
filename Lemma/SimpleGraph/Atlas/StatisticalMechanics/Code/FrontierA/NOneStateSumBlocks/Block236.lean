import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block236
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock236_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block236.lean)
-/
@[path]
private lemma directStateBlock236_checked_eq :
-- imply
  rawMomentDirectBlock 472 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock236 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock236_checked


-- created on 2026-10-23
