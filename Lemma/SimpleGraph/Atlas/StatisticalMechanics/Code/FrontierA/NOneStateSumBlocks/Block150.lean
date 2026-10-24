import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block150
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock150_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block150.lean)
-/
@[path]
private lemma directStateBlock150_checked_eq :
-- imply
  rawMomentDirectBlock 300 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock150 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock150_checked


-- created on 2026-10-23
