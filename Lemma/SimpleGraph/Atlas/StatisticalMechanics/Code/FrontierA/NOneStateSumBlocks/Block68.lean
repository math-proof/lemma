import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block68
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock68_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block68.lean)
-/
@[path]
private lemma directStateBlock68_checked_eq :
-- imply
  rawMomentDirectBlock 136 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock68 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock68_checked


-- created on 2026-10-23
