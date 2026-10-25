import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block55
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock55_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block55.lean)
-/
@[path]
private lemma directStateBlock55_checked_eq :
-- imply
  rawMomentDirectBlock 110 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock55 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock55_checked


-- created on 2026-10-23
