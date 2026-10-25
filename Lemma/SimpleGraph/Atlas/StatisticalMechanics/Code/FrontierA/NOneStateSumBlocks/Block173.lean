import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block173
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock173_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block173.lean)
-/
@[path]
private lemma directStateBlock173_checked_eq :
-- imply
  rawMomentDirectBlock 346 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock173 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock173_checked


-- created on 2026-10-23
