import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block224
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock224_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block224.lean)
-/
@[path]
private lemma directStateBlock224_checked_eq :
-- imply
  rawMomentDirectBlock 448 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock224 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock224_checked


-- created on 2026-10-23
