import Mathlib
import Lemma.Definitions.Def_AlgebraicCurve_ConstantReduction

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

open IsLocalRing

variable {L : Type*} [Field L] (A : ValuationSubring L)
variable (F : Type*) [Field F] [Algebra L F]
variable (Fbar : Type*) [Field Fbar] [Algebra (ResidueField A) Fbar]

structure RegularProlongation where

  integers : ValuationSubring F

  residue : integers →+* Fbar

  algebraMap_mem_iff : ∀ x : L, algebraMap L F x ∈ integers ↔ x ∈ A

  residue_surjective : Function.Surjective residue

  ker_residue : RingHom.ker residue = maximalIdeal integers

  residue_algebraMap : ∀ a : A,
    residue ⟨algebraMap L F a, (algebraMap_mem_iff a).mpr a.2⟩ =
      algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a)

  exists_smul_mem : ∀ f : F, f ≠ 0 → ∃ c : L, ∃ h : c • f ∈ integers, residue ⟨c • f, h⟩ ≠ 0

namespace RegularProlongation

variable {A F Fbar}
variable (R : RegularProlongation A F Fbar)

theorem isUnit_of_residue_ne_zero {f : R.integers} (hf : R.residue f ≠ 0) : IsUnit f := by
  by_contra h
  apply hf
  have hmem : f ∈ maximalIdeal R.integers := (IsLocalRing.mem_maximalIdeal f).mpr h
  rw [← R.ker_residue] at hmem
  exact hmem

theorem residue_ne_zero_of_isUnit {f : R.integers} (hf : IsUnit f) : R.residue f ≠ 0 := by
  intro h0
  have hmem : f ∈ RingHom.ker R.residue := h0
  rw [R.ker_residue] at hmem
  exact (IsLocalRing.mem_maximalIdeal f).mp hmem hf

theorem smul_const_ne_zero {f : F} {c : L} (hc : c • f ∈ R.integers)
    (hres : R.residue ⟨c • f, hc⟩ ≠ 0) : c ≠ 0 := by
  rintro rfl
  apply hres
  have : (⟨(0 : L) • f, hc⟩ : R.integers) = 0 := Subtype.ext (by simp)
  rw [this, map_zero]

end RegularProlongation

namespace ConstantReduction

variable {A F Fbar}

@[reducible] def toRegularProlongation (R : ConstantReduction A F Fbar) : RegularProlongation A F Fbar where
  integers := R.integers
  residue := R.residue
  algebraMap_mem_iff := R.algebraMap_mem_iff
  residue_surjective := R.residue_surjective
  ker_residue := R.ker_residue
  residue_algebraMap := R.residue_algebraMap
  exists_smul_mem := R.exists_smul_mem

@[simp] theorem toRegularProlongation_integers (R : ConstantReduction A F Fbar) :
    R.toRegularProlongation.integers = R.integers := rfl

@[simp] theorem toRegularProlongation_residue (R : ConstantReduction A F Fbar) :
    R.toRegularProlongation.residue = R.residue := rfl

end ConstantReduction

end AlgebraicCurve

end
