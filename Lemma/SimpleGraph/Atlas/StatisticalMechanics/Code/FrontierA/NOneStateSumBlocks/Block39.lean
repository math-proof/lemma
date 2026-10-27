import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block39
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock39_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block39.lean)
-/
@[path]
private lemma directStateBlock39_checked_eq :
-- imply
  rawMomentDirectBlock 78 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock39 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock39_checked


-- created on 2026-10-23
