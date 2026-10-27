import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block86
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock86_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block86.lean)
-/
@[path]
private lemma directStateBlock86_checked_eq :
-- imply
  rawMomentDirectBlock 172 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock86 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock86_checked


-- created on 2026-10-23
