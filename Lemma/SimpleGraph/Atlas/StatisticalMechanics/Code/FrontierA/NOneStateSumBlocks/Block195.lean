import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block195
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock195_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block195.lean)
-/
@[path]
private lemma directStateBlock195_checked_eq :
-- imply
  rawMomentDirectBlock 390 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock195 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock195_checked


-- created on 2026-10-23
