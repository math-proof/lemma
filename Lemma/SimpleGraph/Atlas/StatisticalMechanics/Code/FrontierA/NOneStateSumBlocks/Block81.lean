import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block81
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock81_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block81.lean)
-/
@[path]
private lemma directStateBlock81_checked_eq :
-- imply
  rawMomentDirectBlock 162 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock81 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock81_checked


-- created on 2026-10-23
