import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block205
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock205_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block205.lean)
-/
@[path]
private lemma directStateBlock205_checked_eq :
-- imply
  rawMomentDirectBlock 410 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock205 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock205_checked


-- created on 2026-10-23
