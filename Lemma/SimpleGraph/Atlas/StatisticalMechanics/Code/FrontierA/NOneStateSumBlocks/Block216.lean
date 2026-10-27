import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block216
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock216_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block216.lean)
-/
@[path]
private lemma directStateBlock216_checked_eq :
-- imply
  rawMomentDirectBlock 432 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock216 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock216_checked


-- created on 2026-10-23
