import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block66
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock66_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block66.lean)
-/
@[path]
private lemma directStateBlock66_checked_eq :
-- imply
  rawMomentDirectBlock 132 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock66 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock66_checked


-- created on 2026-10-23
