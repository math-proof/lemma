import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block38
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock38_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block38.lean)
-/
@[path]
private lemma directStateBlock38_checked_eq :
-- imply
  rawMomentDirectBlock 76 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock38 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock38_checked


-- created on 2026-10-23
