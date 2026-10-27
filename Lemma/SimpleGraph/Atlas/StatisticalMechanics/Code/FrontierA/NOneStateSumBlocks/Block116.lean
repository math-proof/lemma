import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block116
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock116_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block116.lean)
-/
@[path]
private lemma directStateBlock116_checked_eq :
-- imply
  rawMomentDirectBlock 232 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock116 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock116_checked


-- created on 2026-10-23
