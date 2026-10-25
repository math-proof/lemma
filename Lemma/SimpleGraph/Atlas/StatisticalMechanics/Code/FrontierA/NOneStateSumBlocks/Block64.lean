import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block64
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock64_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block64.lean)
-/
@[path]
private lemma directStateBlock64_checked_eq :
-- imply
  rawMomentDirectBlock 128 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock64 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock64_checked


-- created on 2026-10-23
