import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block46
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock46_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block46.lean)
-/
@[path]
private lemma directStateBlock46_checked_eq :
-- imply
  rawMomentDirectBlock 92 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock46 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock46_checked


-- created on 2026-10-23
