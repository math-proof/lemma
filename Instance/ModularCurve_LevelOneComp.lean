-- Carved from Lemma/Definitions/Def_ModularCurve_LevelOneComp.lean: instance decls only.
import Mathlib
import Instance.ModularCurve_JZeroSemistableSpecialization
import Lemma.ModularCurve.ModularUnit
import Lemma.ModularCurve.LevelOneComp

set_option autoImplicit false

noncomputable section

namespace ModularCurve

open ValuationSubring

section LevelOneComp

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (q : ℕ)

set_option synthInstance.maxHeartbeats 400000 in
instance LevelOnePhi.instAddCommGroup : AddCommGroup (LevelOnePhi A q) :=
  QuotientAddGroup.Quotient.addCommGroup (levelOneIdentityComponent A q)

end LevelOneComp

end ModularCurve

end
