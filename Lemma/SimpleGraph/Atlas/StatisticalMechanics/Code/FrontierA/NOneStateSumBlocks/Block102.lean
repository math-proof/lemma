import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block102
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock102_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block102.lean)
-/
@[path]
private lemma directStateBlock102_checked_eq :
-- imply
  rawMomentDirectBlock 204 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock102 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock102_checked


-- created on 2026-10-23
