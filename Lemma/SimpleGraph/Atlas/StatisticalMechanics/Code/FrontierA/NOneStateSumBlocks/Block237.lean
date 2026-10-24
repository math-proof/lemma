import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block237
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock237_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block237.lean)
-/
@[path]
private lemma directStateBlock237_checked_eq :
-- imply
  rawMomentDirectBlock 474 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock237 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock237_checked


-- created on 2026-10-23
