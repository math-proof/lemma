import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block130
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock130_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block130.lean)
-/
@[path]
private lemma directStateBlock130_checked_eq :
-- imply
  rawMomentDirectBlock 260 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock130 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock130_checked


-- created on 2026-10-23
