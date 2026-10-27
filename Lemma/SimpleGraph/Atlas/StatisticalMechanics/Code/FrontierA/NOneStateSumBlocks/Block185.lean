import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block185
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock185_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block185.lean)
-/
@[path]
private lemma directStateBlock185_checked_eq :
-- imply
  rawMomentDirectBlock 370 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock185 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock185_checked


-- created on 2026-10-23
