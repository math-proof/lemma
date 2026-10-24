import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block203
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock203_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block203.lean)
-/
@[path]
private lemma directStateBlock203_checked_eq :
-- imply
  rawMomentDirectBlock 406 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock203 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock203_checked


-- created on 2026-10-23
