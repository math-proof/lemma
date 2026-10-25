import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block230
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock230_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block230.lean)
-/
@[path]
private lemma directStateBlock230_checked_eq :
-- imply
  rawMomentDirectBlock 460 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock230 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock230_checked


-- created on 2026-10-23
