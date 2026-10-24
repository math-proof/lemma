import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block186
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock186_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block186.lean)
-/
@[path]
private lemma directStateBlock186_checked_eq :
-- imply
  rawMomentDirectBlock 372 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock186 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock186_checked


-- created on 2026-10-23
