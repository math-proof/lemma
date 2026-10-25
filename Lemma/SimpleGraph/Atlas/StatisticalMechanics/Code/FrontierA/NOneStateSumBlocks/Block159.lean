import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block159
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock159_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block159.lean)
-/
@[path]
private lemma directStateBlock159_checked_eq :
-- imply
  rawMomentDirectBlock 318 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock159 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock159_checked


-- created on 2026-10-23
