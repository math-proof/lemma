import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block85
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock85_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block85.lean)
-/
@[path]
private lemma directStateBlock85_checked_eq :
-- imply
  rawMomentDirectBlock 170 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock85 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock85_checked


-- created on 2026-10-23
