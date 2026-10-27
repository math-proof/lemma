import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block168
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock168_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block168.lean)
-/
@[path]
private lemma directStateBlock168_checked_eq :
-- imply
  rawMomentDirectBlock 336 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock168 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock168_checked


-- created on 2026-10-23
