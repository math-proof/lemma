import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block251
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock251_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block251.lean)
-/
@[path]
private lemma directStateBlock251_checked_eq :
-- imply
  rawMomentDirectBlock 502 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock251 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock251_checked


-- created on 2026-10-23
