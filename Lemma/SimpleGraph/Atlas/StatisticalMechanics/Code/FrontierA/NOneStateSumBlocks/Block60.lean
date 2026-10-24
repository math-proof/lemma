import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block60
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock60_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block60.lean)
-/
@[path]
private lemma directStateBlock60_checked_eq :
-- imply
  rawMomentDirectBlock 120 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock60 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock60_checked


-- created on 2026-10-23
