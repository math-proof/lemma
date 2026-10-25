import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block65
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock65_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block65.lean)
-/
@[path]
private lemma directStateBlock65_checked_eq :
-- imply
  rawMomentDirectBlock 130 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock65 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock65_checked


-- created on 2026-10-23
