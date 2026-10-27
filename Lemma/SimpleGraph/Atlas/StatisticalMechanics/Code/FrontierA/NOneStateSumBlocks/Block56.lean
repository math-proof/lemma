import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block56
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock56_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block56.lean)
-/
@[path]
private lemma directStateBlock56_checked_eq :
-- imply
  rawMomentDirectBlock 112 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock56 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock56_checked


-- created on 2026-10-23
