import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block101
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock101_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block101.lean)
-/
@[path]
private lemma directStateBlock101_checked_eq :
-- imply
  rawMomentDirectBlock 202 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock101 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock101_checked


-- created on 2026-10-23
