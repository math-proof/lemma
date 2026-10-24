import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block198
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock198_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block198.lean)
-/
@[path]
private lemma directStateBlock198_checked_eq :
-- imply
  rawMomentDirectBlock 396 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock198 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock198_checked


-- created on 2026-10-23
