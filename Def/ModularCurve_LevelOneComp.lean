import Mathlib
import Instance.ModularCurve_JZeroSemistableSpecialization
import Lemma.ModularCurve.ModularUnit
import Instance.ModularCurve_LevelOneComp

set_option autoImplicit false

noncomputable section

namespace ModularCurve

open ValuationSubring

section LevelOneComp

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (q : ℕ)

def levelOneIdentityComponent : AddSubgroup ↥(inertiaInvariants A (1 * q)) :=
  (nsmulAddMonoidHom (eisensteinNumerator q) :
    ↥(inertiaInvariants A (1 * q)) →+ ↥(inertiaInvariants A (1 * q))).range


def LevelOnePhi : Type := ↥(inertiaInvariants A (1 * q)) ⧸ levelOneIdentityComponent A q

set_option synthInstance.maxHeartbeats 400000 in

def LevelOnePhi.mk : ↥(inertiaInvariants A (1 * q)) →+ LevelOnePhi A q :=
  QuotientAddGroup.mk' (levelOneIdentityComponent A q)


def levelOneComp {ι : Type*} [Fintype ι] {width : ι → ℕ} (φ : LevelOnePhi A q ≃+ componentGroup width) :
    ↥(inertiaInvariants A (1 * q)) →+ componentGroup width :=
  φ.toAddMonoidHom.comp (LevelOnePhi.mk A q)

end LevelOneComp

end ModularCurve

end
