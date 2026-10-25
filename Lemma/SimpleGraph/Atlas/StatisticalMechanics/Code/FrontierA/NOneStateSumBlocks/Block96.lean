import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block96
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock96_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block96.lean)
-/
@[path]
private lemma directStateBlock96_checked_eq :
-- imply
  rawMomentDirectBlock 192 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock96 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock96_checked


-- created on 2026-10-23
