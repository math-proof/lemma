import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block162
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock162_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block162.lean)
-/
@[path]
private lemma directStateBlock162_checked_eq :
-- imply
  rawMomentDirectBlock 324 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock162 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock162_checked


-- created on 2026-10-23
