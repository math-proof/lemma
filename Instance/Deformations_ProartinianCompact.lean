-- Carved from Lemma/Definitions/Def_Deformations_ProartinianCompact.lean: instance decls only.
import Mathlib
import Class.Deformations_ProartinianCat

set_option autoImplicit false

universe u

open CategoryTheory Function IsLocalRing Filter Topology Set Pointwise


namespace Deformation.ProartinianCat

variable {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞]

instance instFiniteResidueField [Empty.Finite (ResidueField 𝓞)] (A : ProartinianCat 𝓞) :
    Empty.Finite (ResidueField A) :=
  .of_surjective _ (IsResidueAlgebra.algebraMap_bijective 𝓞 A).surjective

instance instCompactSpace [Empty.Finite (ResidueField 𝓞)] (A : ProartinianCat 𝓞) :
    CompactSpace A :=
  IsProartinian.compactSpace_of_finite_residueField

end Deformation.ProartinianCat
