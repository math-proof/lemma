import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block73
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock73_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block73.lean)
-/
@[path]
private lemma directStateBlock73_checked_eq :
-- imply
  rawMomentDirectBlock 146 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock73 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock73_checked


-- created on 2026-10-23
