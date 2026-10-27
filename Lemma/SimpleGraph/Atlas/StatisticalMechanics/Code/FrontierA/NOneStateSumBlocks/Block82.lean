import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block82
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock82_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block82.lean)
-/
@[path]
private lemma directStateBlock82_checked_eq :
-- imply
  rawMomentDirectBlock 164 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock82 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock82_checked


-- created on 2026-10-23
