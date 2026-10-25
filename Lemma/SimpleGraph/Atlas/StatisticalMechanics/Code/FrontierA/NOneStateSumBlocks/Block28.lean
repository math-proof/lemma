import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block28
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock28_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block28.lean)
-/
@[path]
private lemma directStateBlock28_checked_eq :
-- imply
  rawMomentDirectBlock 56 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock28 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock28_checked


-- created on 2026-10-23
