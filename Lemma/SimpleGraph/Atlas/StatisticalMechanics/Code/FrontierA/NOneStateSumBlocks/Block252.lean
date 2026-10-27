import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block252
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock252_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block252.lean)
-/
@[path]
private lemma directStateBlock252_checked_eq :
-- imply
  rawMomentDirectBlock 504 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock252 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock252_checked


-- created on 2026-10-23
