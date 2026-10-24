import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block125
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock125_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block125.lean)
-/
@[path]
private lemma directStateBlock125_checked_eq :
-- imply
  rawMomentDirectBlock 250 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock125 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock125_checked


-- created on 2026-10-23
