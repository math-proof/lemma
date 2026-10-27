import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block167
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock167_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block167.lean)
-/
@[path]
private lemma directStateBlock167_checked_eq :
-- imply
  rawMomentDirectBlock 334 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock167 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock167_checked


-- created on 2026-10-23
