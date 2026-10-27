import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block123
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock123_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block123.lean)
-/
@[path]
private lemma directStateBlock123_checked_eq :
-- imply
  rawMomentDirectBlock 246 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock123 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock123_checked


-- created on 2026-10-23
