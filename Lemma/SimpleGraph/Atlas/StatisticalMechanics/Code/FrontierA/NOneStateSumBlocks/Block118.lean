import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block118
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock118_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block118.lean)
-/
@[path]
private lemma directStateBlock118_checked_eq :
-- imply
  rawMomentDirectBlock 236 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock118 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock118_checked


-- created on 2026-10-23
