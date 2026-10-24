import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block49
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock49_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block49.lean)
-/
@[path]
private lemma directStateBlock49_checked_eq :
-- imply
  rawMomentDirectBlock 98 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock49 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock49_checked


-- created on 2026-10-23
