import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block249
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock249_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block249.lean)
-/
@[path]
private lemma directStateBlock249_checked_eq :
-- imply
  rawMomentDirectBlock 498 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock249 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock249_checked


-- created on 2026-10-23
