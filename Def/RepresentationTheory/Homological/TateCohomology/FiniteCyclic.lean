/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RepresentationTheory/Homological/TateCohomology/FiniteCyclic.lean -/

import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
import Mathlib.RepresentationTheory.Homological.GroupHomology.FiniteCyclic
import Abbrev.RepresentationTheory.Homological.TateCohomology.FiniteCyclic
@[expose] noncomputable section

open CategoryTheory Limits ModuleCat Rep


namespace TateCohomology

universe u

variable {R G : Type u} [CommRing R] [CommGroup G] [Fintype G]

variable (A : Rep R G)

/-- Normalization iso for the `(-1, 0, 1)` boundary short complex. -/
noncomputable def zeroNormIso :
    (tateComplex A).sc' (-1) 0 1 ≅ zeroSC A :=
  ShortComplex.isoMk (groupHomology.chainsIso₀ A)
    (groupCohomology.cochainsIso₀ A) (groupCohomology.cochainsIso₁ A)
    (by
      change (groupHomology.chainsIso₀ A).hom ≫ A.norm.toModuleCatHom =
        A.tateNorm ≫ (groupCohomology.cochainsIso₀ A).hom
      rw [Rep.tateNorm, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id])
    (groupCohomology.comp_d₀₁_eq A)

/-- Normalization iso for the `(-2, -1, 0)` boundary short complex. -/
noncomputable def negOneNormIso :
    (tateComplex A).sc' (-2) (-1) 0 ≅ negOneSC A :=
  ShortComplex.isoMk (groupHomology.chainsIso₁ A)
    (groupHomology.chainsIso₀ A) (groupCohomology.cochainsIso₀ A)
    (groupHomology.comp_d₁₀_eq A)
    (by
      change (groupHomology.chainsIso₀ A).hom ≫ A.norm.toModuleCatHom =
        A.tateNorm ≫ (groupCohomology.cochainsIso₀ A).hom
      rw [Rep.tateNorm, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id])

/-- Degree-zero bridge, ending at the normalized short complex homology. -/
noncomputable def zeroBridge :
    tateCohomology A 0 ≅ (zeroSC A).homology :=
  ((tateComplex A).homologyIsoSc' (-1) 0 1 (by simp) (by simp)).trans
    (ShortComplex.homologyMapIso (zeroNormIso A))

end TateCohomology
