import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block94
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock94_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block94.lean)
-/
@[path]
private lemma directStateBlock94_checked_eq :
-- imply
  rawMomentDirectBlock 188 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock94 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock94_checked


-- created on 2026-10-23
