import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block44
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock44_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block44.lean)
-/
@[path]
private lemma directStateBlock44_checked_eq :
-- imply
  rawMomentDirectBlock 88 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock44 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock44_checked


-- created on 2026-10-23
