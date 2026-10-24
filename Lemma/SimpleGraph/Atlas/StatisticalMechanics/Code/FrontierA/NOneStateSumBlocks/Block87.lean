import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block87
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock87_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block87.lean)
-/
@[path]
private lemma directStateBlock87_checked_eq :
-- imply
  rawMomentDirectBlock 174 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock87 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock87_checked


-- created on 2026-10-23
