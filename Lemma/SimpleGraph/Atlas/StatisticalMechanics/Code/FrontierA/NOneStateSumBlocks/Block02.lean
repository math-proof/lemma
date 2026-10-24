import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block02
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock2_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block02.lean)
-/
@[path]
private lemma directStateBlock2_checked_eq :
-- imply
  rawMomentDirectBlock 4 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock2 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock2_checked


-- created on 2026-10-23
