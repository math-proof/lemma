import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block207
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock207_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block207.lean)
-/
@[path]
private lemma directStateBlock207_checked_eq :
-- imply
  rawMomentDirectBlock 414 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock207 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock207_checked


-- created on 2026-10-23
