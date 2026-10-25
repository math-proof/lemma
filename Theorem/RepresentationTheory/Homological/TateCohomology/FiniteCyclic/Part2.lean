/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RepresentationTheory/Homological/TateCohomology/FiniteCyclic.lean -/

import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
import Mathlib.RepresentationTheory.Homological.GroupHomology.FiniteCyclic
import Def.RepresentationTheory.Homological.TateCohomology.FiniteCyclic.Part2
@[expose] noncomputable section

open CategoryTheory Limits ModuleCat Rep


namespace TateCohomology

universe u

variable {R G : Type u} [CommRing R] [CommGroup G] [Fintype G]

variable (A : Rep R G)

lemma zeroSC_range_map_eq (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    (LinearMap.range (zeroSC A).moduleCatToCycles).map
        (zeroKernelEquiv A g hg).toLinearMap =
      LinearMap.range
        (Rep.FiniteCyclicGroup.normHomCompSub A g).moduleCatToCycles := by
  ext x
  simp only [Submodule.mem_map, LinearMap.mem_range]
  constructor
  · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
    refine ⟨z, ?_⟩
    apply Subtype.ext
    simp [zeroKernelEquiv, zeroSC,
      Rep.FiniteCyclicGroup.normHomCompSub,
      ShortComplex.moduleCatToCycles]
  · rintro ⟨z, rfl⟩
    refine ⟨_, ⟨z, rfl⟩, ?_⟩
    apply Subtype.ext
    simp [zeroKernelEquiv, zeroSC,
      Rep.FiniteCyclicGroup.normHomCompSub,
      ShortComplex.moduleCatToCycles]

end TateCohomology
