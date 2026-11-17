-- Carved from Lemma/Definitions/Def_Deformations_ProartinianCompact.lean: instance decls only.

module

public import Mathlib
public import Class.Deformations_ProartinianCat

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Function IsLocalRing Filter Topology Set Pointwise


namespace Deformation.ProartinianCat

variable {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞]

instance instFiniteResidueField [Finite (ResidueField 𝓞)] (A : ProartinianCat 𝓞) :
    Finite (ResidueField A) :=
  .of_surjective _ (IsResidueAlgebra.algebraMap_bijective 𝓞 A).surjective

instance instCompactSpace [Finite (ResidueField 𝓞)] (A : ProartinianCat 𝓞) :
    CompactSpace A :=
  IsProartinian.compactSpace_of_finite_residueField

end Deformation.ProartinianCat
