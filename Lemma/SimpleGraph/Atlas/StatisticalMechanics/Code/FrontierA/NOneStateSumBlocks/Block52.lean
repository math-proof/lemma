import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block52
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock52_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block52.lean)
-/
@[path]
private lemma directStateBlock52_checked_eq :
-- imply
  rawMomentDirectBlock 104 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock52 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock52_checked


-- created on 2026-10-23
