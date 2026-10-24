import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block57
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock57_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block57.lean)
-/
@[path]
private lemma directStateBlock57_checked_eq :
-- imply
  rawMomentDirectBlock 114 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock57 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock57_checked


-- created on 2026-10-23
