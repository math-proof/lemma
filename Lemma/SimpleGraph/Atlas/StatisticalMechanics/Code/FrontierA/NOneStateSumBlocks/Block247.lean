import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block247
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock247_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block247.lean)
-/
@[path]
private lemma directStateBlock247_checked_eq :
-- imply
  rawMomentDirectBlock 494 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock247 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock247_checked


-- created on 2026-10-23
