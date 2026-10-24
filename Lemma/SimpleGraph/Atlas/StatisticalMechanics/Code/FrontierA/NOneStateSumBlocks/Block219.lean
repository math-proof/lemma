import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block219
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock219_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block219.lean)
-/
@[path]
private lemma directStateBlock219_checked_eq :
-- imply
  rawMomentDirectBlock 438 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock219 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock219_checked


-- created on 2026-10-23
