import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block206
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock206_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block206.lean)
-/
@[path]
private lemma directStateBlock206_checked_eq :
-- imply
  rawMomentDirectBlock 412 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock206 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock206_checked


-- created on 2026-10-23
