import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block103
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock103_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block103.lean)
-/
@[path]
private lemma directStateBlock103_checked_eq :
-- imply
  rawMomentDirectBlock 206 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock103 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock103_checked


-- created on 2026-10-23
