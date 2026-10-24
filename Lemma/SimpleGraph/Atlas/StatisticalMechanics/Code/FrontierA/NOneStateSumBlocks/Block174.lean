import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block174
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock174_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block174.lean)
-/
@[path]
private lemma directStateBlock174_checked_eq :
-- imply
  rawMomentDirectBlock 348 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock174 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock174_checked


-- created on 2026-10-23
