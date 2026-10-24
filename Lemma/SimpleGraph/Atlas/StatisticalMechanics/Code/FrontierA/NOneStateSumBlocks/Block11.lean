import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block11
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock11_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block11.lean)
-/
@[path]
private lemma directStateBlock11_checked_eq :
-- imply
  rawMomentDirectBlock 22 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock11 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock11_checked


-- created on 2026-10-23
