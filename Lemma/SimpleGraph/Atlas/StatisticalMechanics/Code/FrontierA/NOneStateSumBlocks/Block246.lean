import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block246
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock246_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block246.lean)
-/
@[path]
private lemma directStateBlock246_checked_eq :
-- imply
  rawMomentDirectBlock 492 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock246 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock246_checked


-- created on 2026-10-23
