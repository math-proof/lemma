import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block122
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock122_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block122.lean)
-/
@[path]
private lemma directStateBlock122_checked_eq :
-- imply
  rawMomentDirectBlock 244 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock122 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock122_checked


-- created on 2026-10-23
