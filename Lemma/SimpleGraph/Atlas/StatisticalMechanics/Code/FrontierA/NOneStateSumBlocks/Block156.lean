import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block156
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock156_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block156.lean)
-/
@[path]
private lemma directStateBlock156_checked_eq :
-- imply
  rawMomentDirectBlock 312 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock156 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock156_checked


-- created on 2026-10-23
