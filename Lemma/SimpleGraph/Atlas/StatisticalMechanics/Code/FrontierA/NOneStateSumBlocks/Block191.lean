import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block191
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock191_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block191.lean)
-/
@[path]
private lemma directStateBlock191_checked_eq :
-- imply
  rawMomentDirectBlock 382 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock191 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock191_checked


-- created on 2026-10-23
