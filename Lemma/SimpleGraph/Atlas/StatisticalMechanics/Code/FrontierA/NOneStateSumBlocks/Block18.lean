import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block18
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock18_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block18.lean)
-/
@[path]
private lemma directStateBlock18_checked_eq :
-- imply
  rawMomentDirectBlock 36 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock18 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock18_checked


-- created on 2026-10-23
