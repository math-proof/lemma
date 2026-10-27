import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block234
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock234_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block234.lean)
-/
@[path]
private lemma directStateBlock234_checked_eq :
-- imply
  rawMomentDirectBlock 468 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock234 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock234_checked


-- created on 2026-10-23
