import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block50
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock50_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block50.lean)
-/
@[path]
private lemma directStateBlock50_checked_eq :
-- imply
  rawMomentDirectBlock 100 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock50 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock50_checked


-- created on 2026-10-23
