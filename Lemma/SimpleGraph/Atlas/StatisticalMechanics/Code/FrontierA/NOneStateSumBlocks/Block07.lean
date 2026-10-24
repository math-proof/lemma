import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block07
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock7_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block07.lean)
-/
@[path]
private lemma directStateBlock7_checked_eq :
-- imply
  rawMomentDirectBlock 14 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock7 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock7_checked


-- created on 2026-10-23
