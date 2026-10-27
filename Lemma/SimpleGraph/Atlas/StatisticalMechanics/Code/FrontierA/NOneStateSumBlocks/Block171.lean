import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block171
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock171_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block171.lean)
-/
@[path]
private lemma directStateBlock171_checked_eq :
-- imply
  rawMomentDirectBlock 342 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock171 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock171_checked


-- created on 2026-10-23
