import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block240
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock240_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block240.lean)
-/
@[path]
private lemma directStateBlock240_checked_eq :
-- imply
  rawMomentDirectBlock 480 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock240 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock240_checked


-- created on 2026-10-23
