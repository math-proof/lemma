import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block161
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock161_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block161.lean)
-/
@[path]
private lemma directStateBlock161_checked_eq :
-- imply
  rawMomentDirectBlock 322 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock161 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock161_checked


-- created on 2026-10-23
