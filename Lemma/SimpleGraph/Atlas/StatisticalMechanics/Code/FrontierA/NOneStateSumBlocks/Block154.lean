import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block154
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock154_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block154.lean)
-/
@[path]
private lemma directStateBlock154_checked_eq :
-- imply
  rawMomentDirectBlock 308 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock154 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock154_checked


-- created on 2026-10-23
