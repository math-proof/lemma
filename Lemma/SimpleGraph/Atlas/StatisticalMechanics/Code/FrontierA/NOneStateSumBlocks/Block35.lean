import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block35
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock35_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block35.lean)
-/
@[path]
private lemma directStateBlock35_checked_eq :
-- imply
  rawMomentDirectBlock 70 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock35 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock35_checked


-- created on 2026-10-23
