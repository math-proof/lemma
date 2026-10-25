import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block89
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock89_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block89.lean)
-/
@[path]
private lemma directStateBlock89_checked_eq :
-- imply
  rawMomentDirectBlock 178 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock89 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock89_checked


-- created on 2026-10-23
