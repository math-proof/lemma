import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block110
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock110_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block110.lean)
-/
@[path]
private lemma directStateBlock110_checked_eq :
-- imply
  rawMomentDirectBlock 220 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock110 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock110_checked


-- created on 2026-10-23
