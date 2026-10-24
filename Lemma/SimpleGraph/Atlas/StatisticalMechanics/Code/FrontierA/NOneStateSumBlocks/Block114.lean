import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block114
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock114_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block114.lean)
-/
@[path]
private lemma directStateBlock114_checked_eq :
-- imply
  rawMomentDirectBlock 228 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock114 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock114_checked


-- created on 2026-10-23
