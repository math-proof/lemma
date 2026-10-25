-- Carved from Lemma/Definitions/Def_AlgebraicCurve_SemistableModel.lean: instance decls only.
import Mathlib
import Lemma.AlgebraicCurve.SemistableCharts
import Abbrev.AlgebraicCurve_SemistableModel

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing

universe u v w u₁ u₂

namespace AlgebraicCurve


variable {L : Type u} [Field L] (A : ValuationSubring L)
variable (F : Type v) [Field F] [Algebra L F]
variable {ιV : Type u₁} {ιE : Type u₂} (Fbar : ιV → Type w) [∀ i, Field (Fbar i)] [∀ i, Algebra (ResidueField A) (Fbar i)]
variable (C : ∀ i, ComponentChart A F (Fbar i)) (An : ιE → Annulus A F) (src tgt : ιE → ιV)
variable (xs : ∀ e, Place (ResidueField A) (Fbar (src e))) (xt : ∀ e, Place (ResidueField A) (Fbar (tgt e)))


namespace SemistableModel

variable {A F Fbar C An src tgt xs xt}


instance isClosedImmersion_specMap_residue (R : Type u) [CommRing R] [IsLocalRing R] :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective


end SemistableModel

end AlgebraicCurve

end
