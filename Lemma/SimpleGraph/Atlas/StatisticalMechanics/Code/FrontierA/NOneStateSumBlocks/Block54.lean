import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block54
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock54_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block54.lean)
-/
@[path]
private lemma directStateBlock54_checked_eq :
-- imply
  rawMomentDirectBlock 108 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock54 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock54_checked


-- created on 2026-10-23
