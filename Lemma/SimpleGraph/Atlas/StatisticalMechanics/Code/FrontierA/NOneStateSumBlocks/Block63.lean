import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block63
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock63_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block63.lean)
-/
@[path]
private lemma directStateBlock63_checked_eq :
-- imply
  rawMomentDirectBlock 126 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock63 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock63_checked


-- created on 2026-10-23
