/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RepresentationTheory/Homological/TateCohomology/FiniteCyclic.lean -/

import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
import Mathlib.RepresentationTheory.Homological.GroupHomology.FiniteCyclic
import Def.RepresentationTheory.Homological.TateCohomology.FiniteCyclic.Part3
@[expose] noncomputable section

open CategoryTheory Limits ModuleCat Rep


namespace TateCohomology

universe u

variable {R G : Type u} [CommRing R] [CommGroup G] [Fintype G]

variable (A : Rep R G)

lemma negOneSC_range_eq (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    LinearMap.range (negOneSC A).moduleCatToCycles =
      LinearMap.range
        (Rep.FiniteCyclicGroup.subCompNormHom A g).moduleCatToCycles := by
  change LinearMap.range ((groupHomology.d₁₀ A).hom.codRestrict
      (LinearMap.ker A.norm.hom.toLinearMap) _) =
    LinearMap.range ((Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap.codRestrict
      (LinearMap.ker A.norm.hom.toLinearMap) _)
  have hRange : LinearMap.range (groupHomology.d₁₀ A).hom =
      LinearMap.range (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap := by
    rw [groupHomology.range_d₁₀_eq_coinvariantsKer,
      Representation.FiniteCyclicGroup.coinvariantsKer_eq_range A.ρ g hg]
    ext x; simp [Rep.sub_hom]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    have hmem := LinearMap.mem_range_self (groupHomology.d₁₀ A).hom y
    rw [hRange] at hmem
    obtain ⟨z, hz⟩ := hmem
    exact ⟨z, Subtype.ext hz⟩
  · rintro ⟨y, rfl⟩
    have hmem :=
      LinearMap.mem_range_self (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap y
    rw [← hRange] at hmem
    obtain ⟨z, hz⟩ := hmem
    exact ⟨z, Subtype.ext hz⟩

end TateCohomology
