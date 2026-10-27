import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block229
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock229_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block229.lean)
-/
@[path]
private lemma directStateBlock229_checked_eq :
-- imply
  rawMomentDirectBlock 458 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock229 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock229_checked


-- created on 2026-10-23
