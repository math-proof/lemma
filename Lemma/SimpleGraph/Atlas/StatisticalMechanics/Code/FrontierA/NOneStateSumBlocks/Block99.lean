import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block99
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock99_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block99.lean)
-/
@[path]
private lemma directStateBlock99_checked_eq :
-- imply
  rawMomentDirectBlock 198 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock99 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock99_checked


-- created on 2026-10-23
