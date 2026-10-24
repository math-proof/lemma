import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block225
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock225_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block225.lean)
-/
@[path]
private lemma directStateBlock225_checked_eq :
-- imply
  rawMomentDirectBlock 450 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock225 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock225_checked


-- created on 2026-10-23
