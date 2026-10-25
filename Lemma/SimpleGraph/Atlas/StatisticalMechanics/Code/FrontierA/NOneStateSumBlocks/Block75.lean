import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block75
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock75_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block75.lean)
-/
@[path]
private lemma directStateBlock75_checked_eq :
-- imply
  rawMomentDirectBlock 150 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock75 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock75_checked


-- created on 2026-10-23
