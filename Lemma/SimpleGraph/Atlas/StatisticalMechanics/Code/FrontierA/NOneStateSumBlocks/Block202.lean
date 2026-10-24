import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block202
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock202_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block202.lean)
-/
@[path]
private lemma directStateBlock202_checked_eq :
-- imply
  rawMomentDirectBlock 404 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock202 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock202_checked


-- created on 2026-10-23
