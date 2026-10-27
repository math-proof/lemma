import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block157
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock157_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block157.lean)
-/
@[path]
private lemma directStateBlock157_checked_eq :
-- imply
  rawMomentDirectBlock 314 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock157 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock157_checked


-- created on 2026-10-23
