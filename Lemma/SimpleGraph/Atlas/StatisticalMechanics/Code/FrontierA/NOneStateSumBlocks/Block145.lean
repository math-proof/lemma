import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block145
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock145_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block145.lean)
-/
@[path]
private lemma directStateBlock145_checked_eq :
-- imply
  rawMomentDirectBlock 290 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock145 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock145_checked


-- created on 2026-10-23
