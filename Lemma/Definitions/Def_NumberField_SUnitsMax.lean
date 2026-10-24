import Mathlib
import Lemma.Definitions.Def_GroupCohomology_ContinuousUnramified

set_option autoImplicit false

noncomputable section

namespace NumberField.LevelArith

variable (S : Finset Nat.Primes)

def IsSUnitMax (x : (AlgebraicClosure ℚ)ˣ) : Prop :=
  (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧ (x : AlgebraicClosure ℚ) ∈ F) ∧
    ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime (q : ℕ) →
      (x : AlgebraicClosure ℚ) ∈ A ∧ ((x⁻¹ : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ∈ A

def sUnitsMax : Subgroup (AlgebraicClosure ℚ)ˣ where
  carrier := {x | IsSUnitMax S x}
  one_mem' := ⟨⟨⊥, IntermediateField.isUnramifiedOutside_bot S, by simp⟩, fun q _ A _ => ⟨by simp, by simp⟩⟩
  mul_mem' := by
    rintro x y ⟨⟨F, hF, hxF⟩, hx⟩ ⟨⟨F', hF', hyF'⟩, hy⟩
    refine ⟨⟨F ⊔ F', hF.sup hF', ?_⟩, fun q hq A hA => ⟨?_, ?_⟩⟩
    · rw [Units.val_mul]; exact mul_mem ((le_sup_left : F ≤ F ⊔ F') hxF) ((le_sup_right : F' ≤ F ⊔ F') hyF')
    · rw [Units.val_mul]; exact A.toSubring.mul_mem (hx q hq A hA).1 (hy q hq A hA).1
    · rw [mul_inv_rev, Units.val_mul]; exact A.toSubring.mul_mem (hy q hq A hA).2 (hx q hq A hA).2
  inv_mem' := by
    rintro x ⟨⟨F, hF, hxF⟩, hx⟩
    refine ⟨⟨F, hF, ?_⟩, fun q hq A hA => ⟨(hx q hq A hA).2, by simpa using (hx q hq A hA).1⟩⟩
    rw [Units.val_inv_eq_inv_val]; exact inv_mem hxF

theorem mem_sUnitsMax_iff (x : (AlgebraicClosure ℚ)ˣ) : x ∈ sUnitsMax S ↔ IsSUnitMax S x := Iff.rfl

variable (L : IntermediateField ℚ (AlgebraicClosure ℚ))

def sUnitsMaxStable : Subgroup (AlgebraicClosure ℚ)ˣ :=
  ⨅ γ : ↥L.fixingSubgroup, (sUnitsMax S).comap (MulDistribMulAction.toMonoidHom (AlgebraicClosure ℚ)ˣ (γ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)))

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

def sUnitsMaxSubmodule : Submodule ℤ (Additive (AlgebraicClosure ℚ)ˣ) := (Subgroup.toAddSubgroup (sUnitsMaxStable S L)).toIntSubmodule

theorem mem_sUnitsMaxSubmodule (x : Additive (AlgebraicClosure ℚ)ˣ) : x ∈ sUnitsMaxSubmodule S L ↔ Additive.toMul x ∈ sUnitsMaxStable S L := Iff.rfl

abbrev sUnitsMaxRep : Rep ℤ ↥L.fixingSubgroup :=
  Rep.of ((Rep.ofMulDistribMulAction ↥L.fixingSubgroup (AlgebraicClosure ℚ)ˣ).ρ.subrepresentation (sUnitsMaxSubmodule S L)
    fun γ _ hx => smul_mem_sUnitsMaxStable S L γ hx)

abbrev sUnitsMaxRep.val (x : sUnitsMaxRep S L) : (AlgebraicClosure ℚ)ˣ := Additive.toMul x.1

theorem sUnitsMaxRep.val_ρ (γ : ↥L.fixingSubgroup) (x : sUnitsMaxRep S L) :
    sUnitsMaxRep.val S L ((sUnitsMaxRep S L).ρ γ x) = (γ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) • sUnitsMaxRep.val S L x := rfl

end NumberField.LevelArith

end
