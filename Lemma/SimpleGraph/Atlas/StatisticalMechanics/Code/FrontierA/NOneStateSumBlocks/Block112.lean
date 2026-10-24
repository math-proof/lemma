import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block112
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock112_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block112.lean)
-/
@[path]
private lemma directStateBlock112_checked_eq :
-- imply
  rawMomentDirectBlock 224 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock112 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock112_checked


-- created on 2026-10-23
