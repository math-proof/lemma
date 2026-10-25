-- Carved from Lemma/Definitions/Def_Deformations_IsResidueAlgebra.lean: instance decls only.
import Mathlib
import Instance.Mathlib_RingTheory_LocalRing_Defs
import Instance.Deformations_Deformations_Lemmas
import Class.Deformations_IsResidueAlgebra

set_option autoImplicit false

open Function IsLocalRing

variable (𝓞 : Type*) [CommRing 𝓞]


variable (A : Type*) [CommRing A] [Algebra 𝓞 A] [IsLocalRing A]

namespace IsResidueAlgebra

variable [IsResidueAlgebra 𝓞 A]

instance [IsLocalRing 𝓞] : IsResidueAlgebra 𝓞 𝓞 := ⟨IsLocalRing.residue_surjective⟩

section Quotient

instance (I : Ideal A) [Nontrivial (A ⧸ I)] : IsResidueAlgebra 𝓞 (A ⧸ I) where
  isSurjective' :=
    have : IsLocalHom (Ideal.Quotient.mk I) := .of_surjective _ Ideal.Quotient.mk_surjective
    (IsLocalRing.ResidueField.map_surjective _ Ideal.Quotient.mk_surjective).comp
      (IsResidueAlgebra.algebraMap_surjective 𝓞 A)

end Quotient


open IsLocalRing

variable {A}

end IsResidueAlgebra
