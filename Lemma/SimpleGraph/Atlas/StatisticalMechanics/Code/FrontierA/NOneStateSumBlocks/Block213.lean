import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block213
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock213_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block213.lean)
-/
@[path]
private lemma directStateBlock213_checked_eq :
-- imply
  rawMomentDirectBlock 426 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock213 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock213_checked


-- created on 2026-10-23
