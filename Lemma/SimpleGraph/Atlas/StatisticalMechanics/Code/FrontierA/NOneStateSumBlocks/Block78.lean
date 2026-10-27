import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block78
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock78_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block78.lean)
-/
@[path]
private lemma directStateBlock78_checked_eq :
-- imply
  rawMomentDirectBlock 156 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock78 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock78_checked


-- created on 2026-10-23
