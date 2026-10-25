import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block12
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock12_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block12.lean)
-/
@[path]
private lemma directStateBlock12_checked_eq :
-- imply
  rawMomentDirectBlock 24 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock12 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock12_checked


-- created on 2026-10-23
