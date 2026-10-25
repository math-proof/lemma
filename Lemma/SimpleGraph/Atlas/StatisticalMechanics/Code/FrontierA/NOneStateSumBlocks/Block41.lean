import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block41
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock41_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block41.lean)
-/
@[path]
private lemma directStateBlock41_checked_eq :
-- imply
  rawMomentDirectBlock 82 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock41 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock41_checked


-- created on 2026-10-23
