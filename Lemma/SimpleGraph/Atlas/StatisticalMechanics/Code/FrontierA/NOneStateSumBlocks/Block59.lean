import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block59
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock59_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block59.lean)
-/
@[path]
private lemma directStateBlock59_checked_eq :
-- imply
  rawMomentDirectBlock 118 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock59 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock59_checked


-- created on 2026-10-23
