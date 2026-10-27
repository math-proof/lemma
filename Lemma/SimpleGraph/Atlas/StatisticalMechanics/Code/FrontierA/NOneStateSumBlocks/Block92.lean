import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block92
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock92_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block92.lean)
-/
@[path]
private lemma directStateBlock92_checked_eq :
-- imply
  rawMomentDirectBlock 184 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock92 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock92_checked


-- created on 2026-10-23
