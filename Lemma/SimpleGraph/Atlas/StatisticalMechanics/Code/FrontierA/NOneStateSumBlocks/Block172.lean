import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block172
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock172_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block172.lean)
-/
@[path]
private lemma directStateBlock172_checked_eq :
-- imply
  rawMomentDirectBlock 344 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock172 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock172_checked


-- created on 2026-10-23
