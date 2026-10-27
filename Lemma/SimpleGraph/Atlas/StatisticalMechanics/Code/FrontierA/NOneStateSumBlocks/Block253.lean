import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block253
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock253_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block253.lean)
-/
@[path]
private lemma directStateBlock253_checked_eq :
-- imply
  rawMomentDirectBlock 506 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock253 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock253_checked


-- created on 2026-10-23
