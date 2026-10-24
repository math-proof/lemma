import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block08
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock8_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block08.lean)
-/
@[path]
private lemma directStateBlock8_checked_eq :
-- imply
  rawMomentDirectBlock 16 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock8 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock8_checked


-- created on 2026-10-23
