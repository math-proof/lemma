import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block71
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock71_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block71.lean)
-/
@[path]
private lemma directStateBlock71_checked_eq :
-- imply
  rawMomentDirectBlock 142 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock71 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock71_checked


-- created on 2026-10-23
