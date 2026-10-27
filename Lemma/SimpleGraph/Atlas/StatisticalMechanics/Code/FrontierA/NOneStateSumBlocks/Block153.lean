import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block153
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock153_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block153.lean)
-/
@[path]
private lemma directStateBlock153_checked_eq :
-- imply
  rawMomentDirectBlock 306 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock153 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock153_checked


-- created on 2026-10-23
