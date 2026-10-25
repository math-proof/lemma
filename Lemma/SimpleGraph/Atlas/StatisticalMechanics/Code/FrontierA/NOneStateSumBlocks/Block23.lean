import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block23
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock23_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block23.lean)
-/
@[path]
private lemma directStateBlock23_checked_eq :
-- imply
  rawMomentDirectBlock 46 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock23 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock23_checked


-- created on 2026-10-23
