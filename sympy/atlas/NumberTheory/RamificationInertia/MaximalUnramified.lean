/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RamificationInertia/MaximalUnramified.lean -/

import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.Unramified.Basic
import Mathlib.Algebra.Algebra.RestrictScalars

/-! Finite formally unramified intermediate fields relative to a base ring, their
supremum, its universal property, and automorphism invariance. -/

namespace IntermediateField

variable {A K L : Type*} [CommRing A] [Field K] [Field L]
variable [Algebra A K] [Algebra A L] [Algebra K L] [IsScalarTower A K L]

/-- An intermediate field is finite unramified relative to `A` if it is finite over `K` and its
`A`-integral closure is formally unramified over `A`. -/
def IsFiniteUnramified (A : Type*) {K L : Type*} [CommRing A] [Field K] [Field L]
    [Algebra A K] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    (E : IntermediateField K L) : Prop :=
  FiniteDimensional K E ∧ Algebra.FormallyUnramified A (integralClosure A E)

/-- The maximal unramified subextension, defined as the
supremum of all finite unramified intermediate fields. The supremum need not itself be finite or
formally unramified. -/
noncomputable def maximalUnramifiedSubextension (A K L : Type*) [CommRing A]
    [Field K] [Field L] [Algebra A K] [Algebra A L] [Algebra K L]
    [IsScalarTower A K L] : IntermediateField K L :=
  ⨆ (E : IntermediateField K L) (_ : IsFiniteUnramified A E), E

/-- Each qualifying intermediate field lies below the maximal one. -/
theorem le_maximalUnramifiedSubextension {E : IntermediateField K L}
    (hE : IsFiniteUnramified A E) :
    E ≤ maximalUnramifiedSubextension A K L :=
  le_iSup_of_le E (le_iSup_of_le hE le_rfl)

/-- Containment in an arbitrary intermediate field is tested on qualifiers. -/
@[simp]
theorem maximalUnramifiedSubextension_le_iff {F : IntermediateField K L} :
    maximalUnramifiedSubextension A K L ≤ F ↔
      ∀ E : IntermediateField K L, IsFiniteUnramified A E → E ≤ F := by
  constructor
  · intro h E hE
    exact (le_maximalUnramifiedSubextension hE).trans h
  · intro h
    unfold maximalUnramifiedSubextension
    apply iSup_le
    intro E
    apply iSup_le
    intro hE
    exact h E hE

/-- Finite unramifiedness is stable under `K`-automorphisms of `L`. -/
theorem IsFiniteUnramified.map {E : IntermediateField K L}
    (hE : IsFiniteUnramified A E) (σ : L ≃ₐ[K] L) :
    IsFiniteUnramified A (E.map σ.toAlgHom) := by
  obtain ⟨hfin, hunr⟩ := hE
  constructor
  · exact LinearEquiv.finiteDimensional
      (IntermediateField.intermediateFieldMap σ E).toLinearEquiv
  · let e : E ≃ₐ[A] E.map (σ : L →ₐ[K] L) :=
      (IntermediateField.intermediateFieldMap σ E).restrictScalars A
    exact Algebra.FormallyUnramified.of_equiv e.mapIntegralClosure

private theorem map_maximalUnramifiedSubextension_le (σ : L ≃ₐ[K] L) :
    (maximalUnramifiedSubextension A K L).map σ.toAlgHom ≤
      maximalUnramifiedSubextension A K L := by
  unfold maximalUnramifiedSubextension
  rw [IntermediateField.map_iSup]
  apply iSup_le
  intro E
  rw [IntermediateField.map_iSup]
  apply iSup_le
  intro hE
  exact le_maximalUnramifiedSubextension (hE.map σ)

/-- The maximal unramified subextension is invariant under `σ`. -/
theorem map_maximalUnramifiedSubextension (σ : L ≃ₐ[K] L) :
    (maximalUnramifiedSubextension A K L).map σ.toAlgHom =
      maximalUnramifiedSubextension A K L := by
  apply le_antisymm
  · exact map_maximalUnramifiedSubextension_le σ
  · intro x hx
    rw [IntermediateField.mem_map]
    have hx' : σ.symm x ∈ maximalUnramifiedSubextension A K L := by
      apply map_maximalUnramifiedSubextension_le σ.symm
      rw [IntermediateField.mem_map]
      exact ⟨x, hx, by simp⟩
    exact ⟨σ.symm x, hx', by simp⟩

end IntermediateField
