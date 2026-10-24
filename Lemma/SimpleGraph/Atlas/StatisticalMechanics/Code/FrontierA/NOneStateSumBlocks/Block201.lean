import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block201
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock201_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block201.lean)
-/
@[path]
private lemma directStateBlock201_checked_eq :
-- imply
  rawMomentDirectBlock 402 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock201 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock201_checked


-- created on 2026-10-23
