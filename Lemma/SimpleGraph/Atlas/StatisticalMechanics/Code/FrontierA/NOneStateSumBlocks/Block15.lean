import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block15
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock15_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block15.lean)
-/
@[path]
private lemma directStateBlock15_checked_eq :
-- imply
  rawMomentDirectBlock 30 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock15 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock15_checked


-- created on 2026-10-23
