import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block42
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock42_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block42.lean)
-/
@[path]
private lemma directStateBlock42_checked_eq :
-- imply
  rawMomentDirectBlock 84 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock42 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock42_checked


-- created on 2026-10-23
