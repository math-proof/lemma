import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block212
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock212_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block212.lean)
-/
@[path]
private lemma directStateBlock212_checked_eq :
-- imply
  rawMomentDirectBlock 424 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock212 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock212_checked


-- created on 2026-10-23
