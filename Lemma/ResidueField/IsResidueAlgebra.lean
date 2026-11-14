import Mathlib
import Instance.Mathlib_RingTheory_LocalRing_Defs
import Instance.Deformations_Deformations_Lemmas
import Instance.Deformations_IsResidueAlgebra
import Class.Deformations_IsResidueAlgebra

set_option autoImplicit false

open Function IsLocalRing

variable (𝓞 : Type*) [CommRing 𝓞]

local notation3:max "𝓴" 𝓞:max => (IsLocalRing.ResidueField 𝓞)

variable (A : Type*) [CommRing A] [Algebra 𝓞 A] [IsLocalRing A]

namespace IsResidueAlgebra

variable [IsResidueAlgebra 𝓞 A]

lemma algebraMap_surjective : Surjective (algebraMap 𝓞 (𝓴 A)) := isSurjective'

variable [IsLocalRing 𝓞] [IsLocalHom (algebraMap 𝓞 A)] in
lemma algebraMap_bijective : Bijective (algebraMap (𝓴 𝓞) (𝓴 A)) := by
  have hsurj1 := IsLocalRing.residue_surjective (R := 𝓞)
  have hsurj2 := IsResidueAlgebra.algebraMap_surjective 𝓞 A
  exact ⟨(algebraMap (𝓴 𝓞) (𝓴 A)).injective,
    (Function.Surjective.of_comp_iff (algebraMap (𝓴 𝓞) (𝓴 A)) hsurj1).mp hsurj2⟩

variable [IsLocalRing 𝓞] [IsLocalHom (algebraMap 𝓞 A)] in

noncomputable def algEquiv : 𝓴 𝓞 ≃ₐ[𝓞] 𝓴 A :=
  .ofBijective (IsScalarTower.toAlgHom _ _ _) (algebraMap_bijective _ _)

section Quotient

end Quotient

section Relative

variable {𝓞 A}
variable {B : Type*} [CommRing B] [Algebra 𝓞 B] [IsLocalRing B] [IsResidueAlgebra 𝓞 B]

omit [IsLocalRing A] [IsResidueAlgebra 𝓞 A] in
lemma of_restrictScalars [Algebra A B] [IsScalarTower 𝓞 A B] : IsResidueAlgebra A B where
  isSurjective' := by
    refine .of_comp (g := algebraMap 𝓞 A) ?_
    rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq]
    exact IsResidueAlgebra.algebraMap_surjective _ _

end Relative

open IsLocalRing

variable {A}

lemma exists_sub_mem_maximalIdeal (r : A) : ∃ a, r - algebraMap 𝓞 A a ∈ maximalIdeal _ := by
  obtain ⟨a, ha⟩ := IsResidueAlgebra.algebraMap_surjective 𝓞 _ (residue _ r)
  refine ⟨a, ?_⟩
  rw [← Ideal.Quotient.eq]
  exact ha.symm

noncomputable
def preimage (r : A) : 𝓞 := (exists_sub_mem_maximalIdeal 𝓞 r).choose

lemma preimage_spec (r : A) : r - algebraMap 𝓞 A (preimage 𝓞 r) ∈ maximalIdeal _ :=
  (exists_sub_mem_maximalIdeal 𝓞 r).choose_spec

lemma residue_preimage (r : A) : residue _ (algebraMap _ _ (preimage 𝓞 r)) = residue _ r :=
  (Ideal.Quotient.eq.mpr (preimage_spec 𝓞 r)).symm

variable [IsLocalRing 𝓞] [IsLocalHom (algebraMap 𝓞 A)] in
lemma residue_preimage_eq_iff {r : A} {a} :
    residue _ (preimage 𝓞 r) = a ↔ residue _ r = ResidueField.map (algebraMap 𝓞 A) a := by
  rw [← (IsResidueAlgebra.algebraMap_bijective 𝓞 A).1.eq_iff]
  erw [ResidueField.map_residue]
  rw [residue_preimage]
  rfl

end IsResidueAlgebra
