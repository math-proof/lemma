import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block14
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock14_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block14.lean)
-/
@[path]
private lemma directStateBlock14_checked_eq :
-- imply
  rawMomentDirectBlock 28 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock14 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock14_checked


-- created on 2026-10-23
