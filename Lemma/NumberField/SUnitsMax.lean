import Mathlib
import Lemma.GroupCohomology.ContinuousUnramified
import Def.NumberField_SUnitsMax

set_option autoImplicit false

noncomputable section

namespace NumberField.LevelArith

variable (S : Finset Nat.Primes)


theorem mem_sUnitsMax_iff (x : (AlgebraicClosure ℚ)ˣ) : x ∈ sUnitsMax S ↔ IsSUnitMax S x := Iff.rfl

variable (L : IntermediateField ℚ (AlgebraicClosure ℚ))


theorem mem_sUnitsMaxStable_iff (x : (AlgebraicClosure ℚ)ˣ) :
    x ∈ sUnitsMaxStable S L ↔ ∀ γ : ↥L.fixingSubgroup, (γ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) • x ∈ sUnitsMax S := by
  simp only [sUnitsMaxStable, Subgroup.mem_iInf, Subgroup.mem_comap, MulDistribMulAction.toMonoidHom_apply]

theorem sUnitsMaxStable_le : sUnitsMaxStable S L ≤ sUnitsMax S := fun x hx => by
  have h := (mem_sUnitsMaxStable_iff S L x).1 hx 1
  rwa [show ((1 : ↥L.fixingSubgroup) : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) = 1 from rfl, one_smul] at h

theorem smul_mem_sUnitsMaxStable (δ : ↥L.fixingSubgroup) {x : (AlgebraicClosure ℚ)ˣ} (hx : x ∈ sUnitsMaxStable S L) :
    (δ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) • x ∈ sUnitsMaxStable S L := by
  rw [mem_sUnitsMaxStable_iff] at hx ⊢
  intro γ
  rw [← mul_smul]
  exact hx (γ * δ)


theorem mem_sUnitsMaxSubmodule (x : Additive (AlgebraicClosure ℚ)ˣ) : x ∈ sUnitsMaxSubmodule S L ↔ Additive.toMul x ∈ sUnitsMaxStable S L := Iff.rfl

abbrev sUnitsMaxRep : Rep ℤ ↥L.fixingSubgroup :=
  Rep.of ((Rep.ofMulDistribMulAction ↥L.fixingSubgroup (AlgebraicClosure ℚ)ˣ).ρ.subrepresentation (sUnitsMaxSubmodule S L)
    fun γ _ hx => smul_mem_sUnitsMaxStable S L γ hx)

abbrev sUnitsMaxRep.val (x : sUnitsMaxRep S L) : (AlgebraicClosure ℚ)ˣ := Additive.toMul x.1

theorem sUnitsMaxRep.val_ρ (γ : ↥L.fixingSubgroup) (x : sUnitsMaxRep S L) :
    sUnitsMaxRep.val S L ((sUnitsMaxRep S L).ρ γ x) = (γ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) • sUnitsMaxRep.val S L x := rfl

end NumberField.LevelArith

end
