import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block200
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock200_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block200.lean)
-/
@[path]
private lemma directStateBlock200_checked_eq :
-- imply
  rawMomentDirectBlock 400 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock200 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock200_checked


-- created on 2026-10-23
