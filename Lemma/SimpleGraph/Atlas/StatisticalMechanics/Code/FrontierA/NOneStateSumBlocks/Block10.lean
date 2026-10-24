import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block10
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock10_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block10.lean)
-/
@[path]
private lemma directStateBlock10_checked_eq :
-- imply
  rawMomentDirectBlock 20 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock10 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock10_checked


-- created on 2026-10-23
