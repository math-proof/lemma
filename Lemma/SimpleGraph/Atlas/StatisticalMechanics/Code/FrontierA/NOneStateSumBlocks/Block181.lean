import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block181
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock181_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block181.lean)
-/
@[path]
private lemma directStateBlock181_checked_eq :
-- imply
  rawMomentDirectBlock 362 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock181 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock181_checked


-- created on 2026-10-23
