import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block235
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock235_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block235.lean)
-/
@[path]
private lemma directStateBlock235_checked_eq :
-- imply
  rawMomentDirectBlock 470 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock235 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock235_checked


-- created on 2026-10-23
