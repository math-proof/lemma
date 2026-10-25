import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block231
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock231_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block231.lean)
-/
@[path]
private lemma directStateBlock231_checked_eq :
-- imply
  rawMomentDirectBlock 462 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock231 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock231_checked


-- created on 2026-10-23
