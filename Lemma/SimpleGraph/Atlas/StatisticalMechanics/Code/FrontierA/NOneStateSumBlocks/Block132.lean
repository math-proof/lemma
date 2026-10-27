import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block132
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock132_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block132.lean)
-/
@[path]
private lemma directStateBlock132_checked_eq :
-- imply
  rawMomentDirectBlock 264 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock132 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock132_checked


-- created on 2026-10-23
