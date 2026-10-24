import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block111
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock111_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block111.lean)
-/
@[path]
private lemma directStateBlock111_checked_eq :
-- imply
  rawMomentDirectBlock 222 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock111 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock111_checked


-- created on 2026-10-23
