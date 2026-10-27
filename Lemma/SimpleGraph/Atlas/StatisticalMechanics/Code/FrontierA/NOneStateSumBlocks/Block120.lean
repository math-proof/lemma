import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block120
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock120_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block120.lean)
-/
@[path]
private lemma directStateBlock120_checked_eq :
-- imply
  rawMomentDirectBlock 240 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock120 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock120_checked


-- created on 2026-10-23
