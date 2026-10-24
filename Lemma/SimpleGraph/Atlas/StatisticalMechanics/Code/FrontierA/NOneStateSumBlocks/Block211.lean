import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block211
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock211_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block211.lean)
-/
@[path]
private lemma directStateBlock211_checked_eq :
-- imply
  rawMomentDirectBlock 422 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock211 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock211_checked


-- created on 2026-10-23
