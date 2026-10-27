import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block32
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock32_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block32.lean)
-/
@[path]
private lemma directStateBlock32_checked_eq :
-- imply
  rawMomentDirectBlock 64 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock32 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock32_checked


-- created on 2026-10-23
