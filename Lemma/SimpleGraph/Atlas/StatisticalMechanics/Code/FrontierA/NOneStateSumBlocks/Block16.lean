import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block16
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock16_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block16.lean)
-/
@[path]
private lemma directStateBlock16_checked_eq :
-- imply
  rawMomentDirectBlock 32 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock16 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock16_checked


-- created on 2026-10-23
