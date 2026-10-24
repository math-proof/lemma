import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block119
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock119_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block119.lean)
-/
@[path]
private lemma directStateBlock119_checked_eq :
-- imply
  rawMomentDirectBlock 238 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock119 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock119_checked


-- created on 2026-10-23
