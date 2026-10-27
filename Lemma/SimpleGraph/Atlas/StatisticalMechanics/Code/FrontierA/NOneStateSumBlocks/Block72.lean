import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block72
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock72_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block72.lean)
-/
@[path]
private lemma directStateBlock72_checked_eq :
-- imply
  rawMomentDirectBlock 144 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock72 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock72_checked


-- created on 2026-10-23
