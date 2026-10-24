import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block215
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock215_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block215.lean)
-/
@[path]
private lemma directStateBlock215_checked_eq :
-- imply
  rawMomentDirectBlock 430 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock215 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock215_checked


-- created on 2026-10-23
