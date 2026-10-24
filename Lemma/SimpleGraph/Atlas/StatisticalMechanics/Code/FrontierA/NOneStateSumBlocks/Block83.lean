import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block83
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock83_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block83.lean)
-/
@[path]
private lemma directStateBlock83_checked_eq :
-- imply
  rawMomentDirectBlock 166 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock83 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock83_checked


-- created on 2026-10-23
