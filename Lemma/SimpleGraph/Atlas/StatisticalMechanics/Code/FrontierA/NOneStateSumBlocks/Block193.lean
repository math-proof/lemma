import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block193
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock193_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block193.lean)
-/
@[path]
private lemma directStateBlock193_checked_eq :
-- imply
  rawMomentDirectBlock 386 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock193 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock193_checked


-- created on 2026-10-23
