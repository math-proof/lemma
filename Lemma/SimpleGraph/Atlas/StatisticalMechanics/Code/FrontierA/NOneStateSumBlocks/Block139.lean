import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block139
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock139_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block139.lean)
-/
@[path]
private lemma directStateBlock139_checked_eq :
-- imply
  rawMomentDirectBlock 278 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock139 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock139_checked


-- created on 2026-10-23
