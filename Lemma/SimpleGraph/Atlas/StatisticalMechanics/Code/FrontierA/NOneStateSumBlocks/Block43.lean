import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block43
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock43_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block43.lean)
-/
@[path]
private lemma directStateBlock43_checked_eq :
-- imply
  rawMomentDirectBlock 86 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock43 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock43_checked


-- created on 2026-10-23
