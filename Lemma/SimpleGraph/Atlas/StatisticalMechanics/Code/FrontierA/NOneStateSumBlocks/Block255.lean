import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block255
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock255_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block255.lean)
-/
@[path]
private lemma directStateBlock255_checked_eq :
-- imply
  rawMomentDirectBlock 510 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock255 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock255_checked


-- created on 2026-10-23
