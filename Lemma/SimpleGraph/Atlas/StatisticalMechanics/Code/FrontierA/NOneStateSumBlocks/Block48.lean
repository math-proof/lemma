import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block48
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock48_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block48.lean)
-/
@[path]
private lemma directStateBlock48_checked_eq :
-- imply
  rawMomentDirectBlock 96 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock48 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock48_checked


-- created on 2026-10-23
