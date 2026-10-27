import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block189
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock189_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block189.lean)
-/
@[path]
private lemma directStateBlock189_checked_eq :
-- imply
  rawMomentDirectBlock 378 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock189 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock189_checked


-- created on 2026-10-23
