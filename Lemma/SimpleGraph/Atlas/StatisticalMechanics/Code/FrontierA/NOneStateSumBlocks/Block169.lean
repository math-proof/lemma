import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block169
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock169_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block169.lean)
-/
@[path]
private lemma directStateBlock169_checked_eq :
-- imply
  rawMomentDirectBlock 338 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock169 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock169_checked


-- created on 2026-10-23
