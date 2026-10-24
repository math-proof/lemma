import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block204
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock204_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block204.lean)
-/
@[path]
private lemma directStateBlock204_checked_eq :
-- imply
  rawMomentDirectBlock 408 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock204 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock204_checked


-- created on 2026-10-23
