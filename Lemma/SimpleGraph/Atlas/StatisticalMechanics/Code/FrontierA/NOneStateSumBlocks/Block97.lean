import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block97
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock97_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block97.lean)
-/
@[path]
private lemma directStateBlock97_checked_eq :
-- imply
  rawMomentDirectBlock 194 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock97 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock97_checked


-- created on 2026-10-23
