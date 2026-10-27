import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block84
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock84_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block84.lean)
-/
@[path]
private lemma directStateBlock84_checked_eq :
-- imply
  rawMomentDirectBlock 168 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock84 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock84_checked


-- created on 2026-10-23
