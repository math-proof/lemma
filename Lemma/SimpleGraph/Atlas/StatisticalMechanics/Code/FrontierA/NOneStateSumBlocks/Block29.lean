import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block29
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock29_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block29.lean)
-/
@[path]
private lemma directStateBlock29_checked_eq :
-- imply
  rawMomentDirectBlock 58 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock29 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock29_checked


-- created on 2026-10-23
