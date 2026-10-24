import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block91
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock91_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block91.lean)
-/
@[path]
private lemma directStateBlock91_checked_eq :
-- imply
  rawMomentDirectBlock 182 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock91 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock91_checked


-- created on 2026-10-23
