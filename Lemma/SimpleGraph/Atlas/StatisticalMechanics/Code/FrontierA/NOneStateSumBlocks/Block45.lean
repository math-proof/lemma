import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block45
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock45_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block45.lean)
-/
@[path]
private lemma directStateBlock45_checked_eq :
-- imply
  rawMomentDirectBlock 90 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock45 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock45_checked


-- created on 2026-10-23
