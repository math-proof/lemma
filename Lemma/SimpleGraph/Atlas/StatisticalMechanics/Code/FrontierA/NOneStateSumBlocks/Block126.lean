import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block126
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock126_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block126.lean)
-/
@[path]
private lemma directStateBlock126_checked_eq :
-- imply
  rawMomentDirectBlock 252 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock126 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock126_checked


-- created on 2026-10-23
