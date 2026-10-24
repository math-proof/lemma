import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block170
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock170_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block170.lean)
-/
@[path]
private lemma directStateBlock170_checked_eq :
-- imply
  rawMomentDirectBlock 340 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock170 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock170_checked


-- created on 2026-10-23
