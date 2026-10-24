import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block33
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock33_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block33.lean)
-/
@[path]
private lemma directStateBlock33_checked_eq :
-- imply
  rawMomentDirectBlock 66 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock33 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock33_checked


-- created on 2026-10-23
