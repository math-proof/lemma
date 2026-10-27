import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block58
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock58_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block58.lean)
-/
@[path]
private lemma directStateBlock58_checked_eq :
-- imply
  rawMomentDirectBlock 116 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock58 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock58_checked


-- created on 2026-10-23
