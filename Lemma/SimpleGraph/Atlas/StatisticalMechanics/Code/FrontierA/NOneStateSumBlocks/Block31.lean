import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block31
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock31_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block31.lean)
-/
@[path]
private lemma directStateBlock31_checked_eq :
-- imply
  rawMomentDirectBlock 62 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock31 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock31_checked


-- created on 2026-10-23
