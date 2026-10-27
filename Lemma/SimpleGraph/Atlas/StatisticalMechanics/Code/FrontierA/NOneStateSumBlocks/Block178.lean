import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block178
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock178_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block178.lean)
-/
@[path]
private lemma directStateBlock178_checked_eq :
-- imply
  rawMomentDirectBlock 356 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock178 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock178_checked


-- created on 2026-10-23
