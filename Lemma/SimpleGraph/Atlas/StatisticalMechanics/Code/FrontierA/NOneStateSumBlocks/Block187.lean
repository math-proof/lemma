import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block187
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock187_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block187.lean)
-/
@[path]
private lemma directStateBlock187_checked_eq :
-- imply
  rawMomentDirectBlock 374 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock187 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock187_checked


-- created on 2026-10-23
