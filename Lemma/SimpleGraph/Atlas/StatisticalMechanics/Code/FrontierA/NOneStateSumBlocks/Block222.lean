import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block222
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock222_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block222.lean)
-/
@[path]
private lemma directStateBlock222_checked_eq :
-- imply
  rawMomentDirectBlock 444 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock222 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock222_checked


-- created on 2026-10-23
