/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RepresentationTheory/Homological/TateCohomology/FiniteCyclic.lean -/

import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
import Mathlib.RepresentationTheory.Homological.GroupHomology.FiniteCyclic
import Theorem.RepresentationTheory.Homological.TateCohomology.FiniteCyclic.Part2
@[expose] noncomputable section

open CategoryTheory Limits ModuleCat Rep


namespace TateCohomology

universe u

variable {R G : Type u} [CommRing R] [CommGroup G] [Fintype G]

variable (A : Rep R G)

noncomputable def zeroIso (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    tateCohomology A 0 ≅
      (Rep.FiniteCyclicGroup.normHomCompSub A g).homology :=
  zeroBridge A ≪≫
    (zeroSC A).moduleCatHomologyIso ≪≫
    (Submodule.Quotient.equiv _ _ (zeroKernelEquiv A g hg)
      (zeroSC_range_map_eq A g hg)).toModuleIso ≪≫
    (Rep.FiniteCyclicGroup.normHomCompSub A g).moduleCatHomologyIso.symm

/-- Degree-minus-one bridge, ending at the normalized short complex homology. -/
noncomputable def negOneBridge :
    tateCohomology A (-1) ≅ (negOneSC A).homology :=
  ((tateComplex A).homologyIsoSc' (-2) (-1) 0 (by simp) (by simp)).trans
    (ShortComplex.homologyMapIso (negOneNormIso A))

end TateCohomology
