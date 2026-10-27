import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block26
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock26_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block26.lean)
-/
@[path]
private lemma directStateBlock26_checked_eq :
-- imply
  rawMomentDirectBlock 52 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock26 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock26_checked


-- created on 2026-10-23
