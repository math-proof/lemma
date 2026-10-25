import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block128
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock128_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block128.lean)
-/
@[path]
private lemma directStateBlock128_checked_eq :
-- imply
  rawMomentDirectBlock 256 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock128 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock128_checked


-- created on 2026-10-23
