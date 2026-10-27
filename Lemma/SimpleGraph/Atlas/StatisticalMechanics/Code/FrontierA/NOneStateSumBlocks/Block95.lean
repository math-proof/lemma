import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block95
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock95_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block95.lean)
-/
@[path]
private lemma directStateBlock95_checked_eq :
-- imply
  rawMomentDirectBlock 190 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock95 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock95_checked


-- created on 2026-10-23
