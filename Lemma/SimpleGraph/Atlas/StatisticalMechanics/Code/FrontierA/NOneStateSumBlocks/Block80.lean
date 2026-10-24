import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block80
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock80_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block80.lean)
-/
@[path]
private lemma directStateBlock80_checked_eq :
-- imply
  rawMomentDirectBlock 160 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock80 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock80_checked


-- created on 2026-10-23
