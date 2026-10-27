import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block218
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock218_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block218.lean)
-/
@[path]
private lemma directStateBlock218_checked_eq :
-- imply
  rawMomentDirectBlock 436 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock218 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock218_checked


-- created on 2026-10-23
