/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RepresentationTheory/Homological/TateCohomology/FiniteCyclic.lean -/

import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
import Mathlib.RepresentationTheory.Homological.GroupHomology.FiniteCyclic
import Theorem.RepresentationTheory.Homological.TateCohomology.FiniteCyclic
@[expose] noncomputable section

open CategoryTheory Limits ModuleCat Rep


namespace TateCohomology

universe u

variable {R G : Type u} [CommRing R] [CommGroup G] [Fintype G]

variable (A : Rep R G)

noncomputable def zeroKernelEquiv (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    LinearMap.ker (zeroSC A).g.hom ≃ₗ[R]
      LinearMap.ker (Rep.FiniteCyclicGroup.normHomCompSub A g).g.hom :=
  LinearEquiv.ofEq _ _ (zeroSC_ker_eq A g hg)

end TateCohomology
