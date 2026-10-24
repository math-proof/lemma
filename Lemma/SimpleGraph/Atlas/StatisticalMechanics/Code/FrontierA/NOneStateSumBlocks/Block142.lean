import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block142
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock142_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block142.lean)
-/
@[path]
private lemma directStateBlock142_checked_eq :
-- imply
  rawMomentDirectBlock 284 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock142 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock142_checked


-- created on 2026-10-23
