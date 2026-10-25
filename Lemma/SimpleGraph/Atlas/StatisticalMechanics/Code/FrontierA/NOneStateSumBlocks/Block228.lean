import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block228
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock228_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block228.lean)
-/
@[path]
private lemma directStateBlock228_checked_eq :
-- imply
  rawMomentDirectBlock 456 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock228 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock228_checked


-- created on 2026-10-23
