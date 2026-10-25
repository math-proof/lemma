/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RepresentationTheory/Homological/TateCohomology/FiniteCyclic.lean -/

import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
import Mathlib.RepresentationTheory.Homological.GroupHomology.FiniteCyclic
import Def.RepresentationTheory.Homological.TateCohomology.FiniteCyclic
@[expose] noncomputable section

open CategoryTheory Limits ModuleCat Rep


namespace TateCohomology

universe u

variable {R G : Type u} [CommRing R] [CommGroup G] [Fintype G]

variable (A : Rep R G)

lemma zeroSC_ker_eq (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    LinearMap.ker (zeroSC A).g.hom =
      LinearMap.ker (Rep.FiniteCyclicGroup.normHomCompSub A g).g.hom := by
  change LinearMap.ker (groupCohomology.d₀₁ A).hom =
    LinearMap.ker (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap
  rw [groupCohomology.d₀₁_ker_eq_invariants]
  ext x
  simpa [Rep.sub_hom, sub_eq_zero] using
    Representation.mem_invariants_iff_of_forall_mem_zpowers A.ρ g hg x

end TateCohomology
