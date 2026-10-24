import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block30
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock30_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block30.lean)
-/
@[path]
private lemma directStateBlock30_checked_eq :
-- imply
  rawMomentDirectBlock 60 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock30 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock30_checked


-- created on 2026-10-23
