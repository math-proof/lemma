import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block182
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock182_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block182.lean)
-/
@[path]
private lemma directStateBlock182_checked_eq :
-- imply
  rawMomentDirectBlock 364 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock182 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock182_checked


-- created on 2026-10-23
