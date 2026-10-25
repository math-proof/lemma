import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block208
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock208_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block208.lean)
-/
@[path]
private lemma directStateBlock208_checked_eq :
-- imply
  rawMomentDirectBlock 416 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock208 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock208_checked


-- created on 2026-10-23
