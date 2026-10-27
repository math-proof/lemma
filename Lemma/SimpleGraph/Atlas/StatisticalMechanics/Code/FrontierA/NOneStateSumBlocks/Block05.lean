import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block05
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock5_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block05.lean)
-/
@[path]
private lemma directStateBlock5_checked_eq :
-- imply
  rawMomentDirectBlock 10 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock5 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock5_checked


-- created on 2026-10-23
