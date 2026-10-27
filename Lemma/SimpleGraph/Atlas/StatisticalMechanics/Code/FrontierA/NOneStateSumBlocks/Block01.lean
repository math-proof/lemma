import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block01
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock1_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block01.lean)
-/
@[path]
private lemma directStateBlock1_checked_eq :
-- imply
  rawMomentDirectBlock 2 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock1 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock1_checked


-- created on 2026-10-23
