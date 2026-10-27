import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block21
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[directStateBlock21_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block21.lean)
-/
@[path]
private lemma directStateBlock21_checked_eq :
-- imply
  rawMomentDirectBlock 42 2 = rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock21 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.directStateBlock21_checked


-- created on 2026-10-23
