import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block217
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock217_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block217.lean)
-/
@[path]
private lemma directStateBlock217_checked_eq :
-- imply
  rawMomentDirectBlock 434 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock217 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock217_checked


-- created on 2026-10-23
