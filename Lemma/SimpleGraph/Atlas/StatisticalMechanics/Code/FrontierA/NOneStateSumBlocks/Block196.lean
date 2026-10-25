import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block196
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock196_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block196.lean)
-/
@[path]
private lemma directStateBlock196_checked_eq :
-- imply
  rawMomentDirectBlock 392 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock196 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock196_checked


-- created on 2026-10-23
