import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block152
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock152_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block152.lean)
-/
@[path]
private lemma directStateBlock152_checked_eq :
-- imply
  rawMomentDirectBlock 304 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock152 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock152_checked


-- created on 2026-10-23
