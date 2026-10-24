import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block107
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock107_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block107.lean)
-/
@[path]
private lemma directStateBlock107_checked_eq :
-- imply
  rawMomentDirectBlock 214 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock107 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock107_checked


-- created on 2026-10-23
