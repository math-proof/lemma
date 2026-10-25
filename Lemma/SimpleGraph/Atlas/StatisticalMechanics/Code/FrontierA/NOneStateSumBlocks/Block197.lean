import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block197
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock197_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block197.lean)
-/
@[path]
private lemma directStateBlock197_checked_eq :
-- imply
  rawMomentDirectBlock 394 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock197 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock197_checked


-- created on 2026-10-23
