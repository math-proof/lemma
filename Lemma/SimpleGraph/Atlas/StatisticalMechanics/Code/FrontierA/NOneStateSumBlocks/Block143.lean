import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block143
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock143_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block143.lean)
-/
@[path]
private lemma directStateBlock143_checked_eq :
-- imply
  rawMomentDirectBlock 286 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock143 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock143_checked


-- created on 2026-10-23
