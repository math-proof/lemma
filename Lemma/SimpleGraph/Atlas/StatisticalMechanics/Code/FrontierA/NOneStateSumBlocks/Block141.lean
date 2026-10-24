import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block141
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock141_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block141.lean)
-/
@[path]
private lemma directStateBlock141_checked_eq :
-- imply
  rawMomentDirectBlock 282 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock141 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock141_checked


-- created on 2026-10-23
