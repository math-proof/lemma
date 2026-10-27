import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block158
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock158_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block158.lean)
-/
@[path]
private lemma directStateBlock158_checked_eq :
-- imply
  rawMomentDirectBlock 316 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock158 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock158_checked


-- created on 2026-10-23
