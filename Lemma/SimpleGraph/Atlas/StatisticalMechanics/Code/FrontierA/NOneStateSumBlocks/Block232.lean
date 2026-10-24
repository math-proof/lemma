import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block232
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock232_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block232.lean)
-/
@[path]
private lemma directStateBlock232_checked_eq :
-- imply
  rawMomentDirectBlock 464 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock232 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock232_checked


-- created on 2026-10-23
