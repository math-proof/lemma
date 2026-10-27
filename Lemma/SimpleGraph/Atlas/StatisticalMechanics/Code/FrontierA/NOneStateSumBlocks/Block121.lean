import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block121
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock121_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block121.lean)
-/
@[path]
private lemma directStateBlock121_checked_eq :
-- imply
  rawMomentDirectBlock 242 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock121 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock121_checked


-- created on 2026-10-23
