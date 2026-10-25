import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block227
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock227_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block227.lean)
-/
@[path]
private lemma directStateBlock227_checked_eq :
-- imply
  rawMomentDirectBlock 454 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock227 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock227_checked


-- created on 2026-10-23
