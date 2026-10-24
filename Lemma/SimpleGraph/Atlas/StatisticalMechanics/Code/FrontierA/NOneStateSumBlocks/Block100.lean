import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block100
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock100_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block100.lean)
-/
@[path]
private lemma directStateBlock100_checked_eq :
-- imply
  rawMomentDirectBlock 200 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock100 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock100_checked


-- created on 2026-10-23
