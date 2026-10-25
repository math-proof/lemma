import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block188
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock188_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block188.lean)
-/
@[path]
private lemma directStateBlock188_checked_eq :
-- imply
  rawMomentDirectBlock 376 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock188 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock188_checked


-- created on 2026-10-23
