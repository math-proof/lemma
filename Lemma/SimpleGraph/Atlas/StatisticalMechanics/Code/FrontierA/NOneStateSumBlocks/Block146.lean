import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block146
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock146_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block146.lean)
-/
@[path]
private lemma directStateBlock146_checked_eq :
-- imply
  rawMomentDirectBlock 292 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock146 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock146_checked


-- created on 2026-10-23
