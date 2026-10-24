import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block164
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock164_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block164.lean)
-/
@[path]
private lemma directStateBlock164_checked_eq :
-- imply
  rawMomentDirectBlock 328 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock164 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock164_checked


-- created on 2026-10-23
