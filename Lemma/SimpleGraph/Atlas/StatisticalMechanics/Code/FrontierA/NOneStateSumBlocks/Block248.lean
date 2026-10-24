import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block248
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock248_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block248.lean)
-/
@[path]
private lemma directStateBlock248_checked_eq :
-- imply
  rawMomentDirectBlock 496 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock248 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock248_checked


-- created on 2026-10-23
