import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block113
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock113_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block113.lean)
-/
@[path]
private lemma directStateBlock113_checked_eq :
-- imply
  rawMomentDirectBlock 226 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock113 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock113_checked


-- created on 2026-10-23
