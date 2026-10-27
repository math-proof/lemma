import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block233
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock233_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block233.lean)
-/
@[path]
private lemma directStateBlock233_checked_eq :
-- imply
  rawMomentDirectBlock 466 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock233 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock233_checked


-- created on 2026-10-23
