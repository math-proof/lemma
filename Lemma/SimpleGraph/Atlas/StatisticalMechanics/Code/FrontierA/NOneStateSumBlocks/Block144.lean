import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block144
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock144_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block144.lean)
-/
@[path]
private lemma directStateBlock144_checked_eq :
-- imply
  rawMomentDirectBlock 288 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock144 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock144_checked


-- created on 2026-10-23
