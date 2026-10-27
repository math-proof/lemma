import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block24
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock24_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block24.lean)
-/
@[path]
private lemma directStateBlock24_checked_eq :
-- imply
  rawMomentDirectBlock 48 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock24 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock24_checked


-- created on 2026-10-23
