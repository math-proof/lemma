import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block51
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock51_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block51.lean)
-/
@[path]
private lemma directStateBlock51_checked_eq :
-- imply
  rawMomentDirectBlock 102 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock51 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock51_checked


-- created on 2026-10-23
