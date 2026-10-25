import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block77
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock77_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block77.lean)
-/
@[path]
private lemma directStateBlock77_checked_eq :
-- imply
  rawMomentDirectBlock 154 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock77 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock77_checked


-- created on 2026-10-23
