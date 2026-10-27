import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block79
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock79_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block79.lean)
-/
@[path]
private lemma directStateBlock79_checked_eq :
-- imply
  rawMomentDirectBlock 158 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock79 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock79_checked


-- created on 2026-10-23
