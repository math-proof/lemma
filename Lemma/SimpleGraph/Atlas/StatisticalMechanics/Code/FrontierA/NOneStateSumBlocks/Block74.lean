import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block74
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock74_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block74.lean)
-/
@[path]
private lemma directStateBlock74_checked_eq :
-- imply
  rawMomentDirectBlock 148 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock74 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock74_checked


-- created on 2026-10-23
