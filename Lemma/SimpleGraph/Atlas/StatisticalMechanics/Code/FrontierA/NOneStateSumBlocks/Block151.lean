import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block151
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock151_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block151.lean)
-/
@[path]
private lemma directStateBlock151_checked_eq :
-- imply
  rawMomentDirectBlock 302 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock151 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock151_checked


-- created on 2026-10-23
