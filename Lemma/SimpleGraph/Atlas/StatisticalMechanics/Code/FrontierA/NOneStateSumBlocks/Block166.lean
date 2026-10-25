import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block166
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock166_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block166.lean)
-/
@[path]
private lemma directStateBlock166_checked_eq :
-- imply
  rawMomentDirectBlock 332 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock166 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock166_checked


-- created on 2026-10-23
