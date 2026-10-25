-- Carved from Lemma/Definitions/Def_AlgebraicGeometry_AdicThickening.lean: instance decls only.
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Lemma.AlgebraicGeometry.AdicThickening

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (I : Ideal R)

instance isClosedImmersion_adicThickeningι (n : ℕ) : IsClosedImmersion (adicThickeningι f I n) := by
  have : IsClosedImmersion (adicThickeningBase I n) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  exact MorphismProperty.pullback_fst _ _ this

end AlgebraicGeometry

end
