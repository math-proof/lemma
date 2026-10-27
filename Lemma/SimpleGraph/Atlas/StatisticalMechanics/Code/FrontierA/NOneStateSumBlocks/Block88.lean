import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block88
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock88_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block88.lean)
-/
@[path]
private lemma directStateBlock88_checked_eq :
-- imply
  rawMomentDirectBlock 176 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock88 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock88_checked


-- created on 2026-10-23
