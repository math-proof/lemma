import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block53
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock53_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block53.lean)
-/
@[path]
private lemma directStateBlock53_checked_eq :
-- imply
  rawMomentDirectBlock 106 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock53 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock53_checked


-- created on 2026-10-23
