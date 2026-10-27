import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block242
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock242_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block242.lean)
-/
@[path]
private lemma directStateBlock242_checked_eq :
-- imply
  rawMomentDirectBlock 484 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock242 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock242_checked


-- created on 2026-10-23
