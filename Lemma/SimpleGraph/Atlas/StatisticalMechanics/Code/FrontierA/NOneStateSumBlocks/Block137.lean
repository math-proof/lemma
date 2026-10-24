import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block137
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock137_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block137.lean)
-/
@[path]
private lemma directStateBlock137_checked_eq :
-- imply
  rawMomentDirectBlock 274 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock137 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock137_checked


-- created on 2026-10-23
