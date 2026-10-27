import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block134
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock134_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block134.lean)
-/
@[path]
private lemma directStateBlock134_checked_eq :
-- imply
  rawMomentDirectBlock 268 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock134 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock134_checked


-- created on 2026-10-23
