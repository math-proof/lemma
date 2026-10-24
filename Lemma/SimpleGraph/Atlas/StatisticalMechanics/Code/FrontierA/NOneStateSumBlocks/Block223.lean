import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block223
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock223_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block223.lean)
-/
@[path]
private lemma directStateBlock223_checked_eq :
-- imply
  rawMomentDirectBlock 446 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock223 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock223_checked


-- created on 2026-10-23
