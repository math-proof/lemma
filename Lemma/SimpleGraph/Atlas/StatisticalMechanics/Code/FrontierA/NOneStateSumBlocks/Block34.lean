import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block34
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock34_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block34.lean)
-/
@[path]
private lemma directStateBlock34_checked_eq :
-- imply
  rawMomentDirectBlock 68 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock34 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock34_checked


-- created on 2026-10-23
