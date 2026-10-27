import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block175
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock175_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block175.lean)
-/
@[path]
private lemma directStateBlock175_checked_eq :
-- imply
  rawMomentDirectBlock 350 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock175 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock175_checked


-- created on 2026-10-23
