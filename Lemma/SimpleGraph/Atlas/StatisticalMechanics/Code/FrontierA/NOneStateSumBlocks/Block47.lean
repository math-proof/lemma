import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block47
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock47_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block47.lean)
-/
@[path]
private lemma directStateBlock47_checked_eq :
-- imply
  rawMomentDirectBlock 94 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock47 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock47_checked


-- created on 2026-10-23
