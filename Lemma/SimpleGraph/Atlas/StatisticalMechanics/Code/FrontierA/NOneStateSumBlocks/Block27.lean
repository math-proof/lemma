import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block27
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock27_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block27.lean)
-/
@[path]
private lemma directStateBlock27_checked_eq :
-- imply
  rawMomentDirectBlock 54 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock27 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock27_checked


-- created on 2026-10-23
