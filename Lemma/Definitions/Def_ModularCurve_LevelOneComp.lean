import Mathlib
import Lemma.Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Lemma.Definitions.Def_ModularCurve_ModularUnit

set_option autoImplicit false

noncomputable section

namespace ModularCurve

open ValuationSubring

section LevelOneComp

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (q : ℕ)

def levelOneIdentityComponent : AddSubgroup ↥(inertiaInvariants A (1 * q)) :=
  (nsmulAddMonoidHom (eisensteinNumerator q) :
    ↥(inertiaInvariants A (1 * q)) →+ ↥(inertiaInvariants A (1 * q))).range

theorem mem_levelOneIdentityComponent (x : ↥(inertiaInvariants A (1 * q))) :
    x ∈ levelOneIdentityComponent A q ↔
      ∃ y : ↥(inertiaInvariants A (1 * q)), eisensteinNumerator q • y = x := by
  simp [levelOneIdentityComponent, AddMonoidHom.mem_range]

def LevelOnePhi : Type := ↥(inertiaInvariants A (1 * q)) ⧸ levelOneIdentityComponent A q

set_option synthInstance.maxHeartbeats 400000 in
instance LevelOnePhi.instAddCommGroup : AddCommGroup (LevelOnePhi A q) :=
  QuotientAddGroup.Quotient.addCommGroup (levelOneIdentityComponent A q)

set_option synthInstance.maxHeartbeats 400000 in

def LevelOnePhi.mk : ↥(inertiaInvariants A (1 * q)) →+ LevelOnePhi A q :=
  QuotientAddGroup.mk' (levelOneIdentityComponent A q)

set_option synthInstance.maxHeartbeats 400000 in
theorem LevelOnePhi.mk_eq_zero_iff (x : ↥(inertiaInvariants A (1 * q))) :
    LevelOnePhi.mk A q x = 0 ↔ ∃ y : ↥(inertiaInvariants A (1 * q)), eisensteinNumerator q • y = x := by
  rw [← mem_levelOneIdentityComponent]
  exact QuotientAddGroup.eq_zero_iff x

theorem LevelOnePhi.mk_surjective : Function.Surjective (LevelOnePhi.mk A q) :=
  QuotientAddGroup.mk'_surjective _

def levelOneComp {ι : Type*} [Fintype ι] {width : ι → ℕ} (φ : LevelOnePhi A q ≃+ componentGroup width) :
    ↥(inertiaInvariants A (1 * q)) →+ componentGroup width :=
  φ.toAddMonoidHom.comp (LevelOnePhi.mk A q)

theorem levelOneComp_apply {ι : Type*} [Fintype ι] {width : ι → ℕ} (φ : LevelOnePhi A q ≃+ componentGroup width)
    (x : ↥(inertiaInvariants A (1 * q))) :
    levelOneComp A q φ x = φ (LevelOnePhi.mk A q x) := rfl

theorem levelOneComp_eq_zero_iff {ι : Type*} [Fintype ι] {width : ι → ℕ}
    (φ : LevelOnePhi A q ≃+ componentGroup width) (x : ↥(inertiaInvariants A (1 * q))) :
    levelOneComp A q φ x = 0 ↔ ∃ y : ↥(inertiaInvariants A (1 * q)), eisensteinNumerator q • y = x := by
  rw [levelOneComp_apply, AddEquiv.map_eq_zero_iff, LevelOnePhi.mk_eq_zero_iff]

theorem levelOneComp_surjective {ι : Type*} [Fintype ι] {width : ι → ℕ}
    (φ : LevelOnePhi A q ≃+ componentGroup width) : Function.Surjective (levelOneComp A q φ) :=
  φ.surjective.comp (LevelOnePhi.mk_surjective A q)

end LevelOneComp

end ModularCurve

end
