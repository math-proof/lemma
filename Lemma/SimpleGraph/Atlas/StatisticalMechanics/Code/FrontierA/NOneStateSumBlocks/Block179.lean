import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block179
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock179_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block179.lean)
-/
@[path]
private lemma directStateBlock179_checked_eq :
-- imply
  rawMomentDirectBlock 358 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock179 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock179_checked


-- created on 2026-10-23
