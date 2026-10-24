import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block115
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock115_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block115.lean)
-/
@[path]
private lemma directStateBlock115_checked_eq :
-- imply
  rawMomentDirectBlock 230 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock115 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock115_checked


-- created on 2026-10-23
