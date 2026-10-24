import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block117
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock117_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block117.lean)
-/
@[path]
private lemma directStateBlock117_checked_eq :
-- imply
  rawMomentDirectBlock 234 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock117 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock117_checked


-- created on 2026-10-23
