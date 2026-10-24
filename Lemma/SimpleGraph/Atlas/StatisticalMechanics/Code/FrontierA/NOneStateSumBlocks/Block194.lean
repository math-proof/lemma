import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block194
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock194_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block194.lean)
-/
@[path]
private lemma directStateBlock194_checked_eq :
-- imply
  rawMomentDirectBlock 388 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock194 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock194_checked


-- created on 2026-10-23
