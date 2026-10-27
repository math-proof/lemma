import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block93
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock93_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block93.lean)
-/
@[path]
private lemma directStateBlock93_checked_eq :
-- imply
  rawMomentDirectBlock 186 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock93 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock93_checked


-- created on 2026-10-23
