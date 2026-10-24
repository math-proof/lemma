import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block69
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock69_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block69.lean)
-/
@[path]
private lemma directStateBlock69_checked_eq :
-- imply
  rawMomentDirectBlock 138 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock69 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock69_checked


-- created on 2026-10-23
