import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block250
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock250_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block250.lean)
-/
@[path]
private lemma directStateBlock250_checked_eq :
-- imply
  rawMomentDirectBlock 500 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock250 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock250_checked


-- created on 2026-10-23
