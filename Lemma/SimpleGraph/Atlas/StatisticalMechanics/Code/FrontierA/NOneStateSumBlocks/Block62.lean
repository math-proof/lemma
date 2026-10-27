import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block62
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock62_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block62.lean)
-/
@[path]
private lemma directStateBlock62_checked_eq :
-- imply
  rawMomentDirectBlock 124 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock62 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock62_checked


-- created on 2026-10-23
