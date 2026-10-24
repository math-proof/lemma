import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block183
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock183_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block183.lean)
-/
@[path]
private lemma directStateBlock183_checked_eq :
-- imply
  rawMomentDirectBlock 366 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock183 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock183_checked


-- created on 2026-10-23
