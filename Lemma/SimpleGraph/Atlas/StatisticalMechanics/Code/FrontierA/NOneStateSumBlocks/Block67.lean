import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block67
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock67_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block67.lean)
-/
@[path]
private lemma directStateBlock67_checked_eq :
-- imply
  rawMomentDirectBlock 134 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock67 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock67_checked


-- created on 2026-10-23
