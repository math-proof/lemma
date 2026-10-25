/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RepresentationTheory/Homological/TateCohomology/FiniteCyclic.lean -/

import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
import Mathlib.RepresentationTheory.Homological.GroupHomology.FiniteCyclic
@[expose] noncomputable section

open CategoryTheory Limits ModuleCat Rep


namespace TateCohomology

universe u

variable {R G : Type u} [CommRing R] [CommGroup G] [Fintype G]

variable (A : Rep R G)

/-- Normalized degree-zero short complex. -/
noncomputable abbrev zeroSC : ShortComplex (ModuleCat R) :=
  ShortComplex.mk A.norm.toModuleCatHom
    (groupCohomology.d₀₁ A) (Rep.norm_comp_d_eq_zero A)

/-- Normalized degree-minus-one short complex. -/
noncomputable abbrev negOneSC : ShortComplex (ModuleCat R) :=
  ShortComplex.mk (groupHomology.d₁₀ A)
    A.norm.toModuleCatHom (Rep.comp_eq_zero A)

end TateCohomology
