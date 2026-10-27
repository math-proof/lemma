import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block131
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock131_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block131.lean)
-/
@[path]
private lemma directStateBlock131_checked_eq :
-- imply
  rawMomentDirectBlock 262 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock131 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock131_checked


-- created on 2026-10-23
