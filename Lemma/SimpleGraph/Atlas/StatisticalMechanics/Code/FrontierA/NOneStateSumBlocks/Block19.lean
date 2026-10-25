import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block19
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock19_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block19.lean)
-/
@[path]
private lemma directStateBlock19_checked_eq :
-- imply
  rawMomentDirectBlock 38 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock19 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock19_checked


-- created on 2026-10-23
