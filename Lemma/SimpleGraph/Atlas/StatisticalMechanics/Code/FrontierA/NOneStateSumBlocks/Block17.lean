import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block17
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock17_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block17.lean)
-/
@[path]
private lemma directStateBlock17_checked_eq :
-- imply
  rawMomentDirectBlock 34 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock17 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock17_checked


-- created on 2026-10-23
