import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block36
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock36_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block36.lean)
-/
@[path]
private lemma directStateBlock36_checked_eq :
-- imply
  rawMomentDirectBlock 72 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock36 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock36_checked


-- created on 2026-10-23
