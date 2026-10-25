import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block226
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock226_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block226.lean)
-/
@[path]
private lemma directStateBlock226_checked_eq :
-- imply
  rawMomentDirectBlock 452 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock226 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock226_checked


-- created on 2026-10-23
