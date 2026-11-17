/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RepresentationTheory/Homological/TateCohomology/FiniteCyclic.lean -/

module

public import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
public import Mathlib.RepresentationTheory.Homological.GroupHomology.FiniteCyclic
public import Theorem.RepresentationTheory.Homological.TateCohomology.FiniteCyclic

@[expose] public section

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
