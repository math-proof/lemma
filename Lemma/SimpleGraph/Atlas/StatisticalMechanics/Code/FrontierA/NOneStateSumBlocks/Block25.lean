import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block25
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock25_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block25.lean)
-/
@[path]
private lemma directStateBlock25_checked_eq :
-- imply
  rawMomentDirectBlock 50 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock25 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock25_checked


-- created on 2026-10-23
