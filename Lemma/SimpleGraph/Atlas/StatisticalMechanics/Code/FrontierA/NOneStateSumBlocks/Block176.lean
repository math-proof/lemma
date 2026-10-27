import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block176
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock176_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block176.lean)
-/
@[path]
private lemma directStateBlock176_checked_eq :
-- imply
  rawMomentDirectBlock 352 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock176 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock176_checked


-- created on 2026-10-23
