import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block209
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock209_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block209.lean)
-/
@[path]
private lemma directStateBlock209_checked_eq :
-- imply
  rawMomentDirectBlock 418 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock209 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock209_checked


-- created on 2026-10-23
