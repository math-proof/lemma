import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block190
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock190_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block190.lean)
-/
@[path]
private lemma directStateBlock190_checked_eq :
-- imply
  rawMomentDirectBlock 380 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock190 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock190_checked


-- created on 2026-10-23
