import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block148
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock148_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block148.lean)
-/
@[path]
private lemma directStateBlock148_checked_eq :
-- imply
  rawMomentDirectBlock 296 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock148 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock148_checked


-- created on 2026-10-23
