-- Carved from Lemma/Definitions/Def_AlgebraicGeometry_RelSubPicGlue.lean: instance decls only.
import Mathlib
import Lemma.CategoryTheory.OverTotalPresheaf
import Instance.AlgebraicGeometry_LocalRepresentabilityULift
import Def.AlgebraicGeometry_RelSubPicPresheaf
import Lemma.AlgebraicGeometry.RelSubPicGlue

set_option autoImplicit false

universe w v u


namespace AlgebraicGeometry.RelPicard

open CategoryTheory CategoryTheory.Limits NeronModelInfra GoodReductionJacobian Opposite

variable {R : Type u} [CommRing R] {C : Scheme.{u}}

section glue

variable (hG : Presieve.IsSheaf (Scheme.zariskiTopology.over (Spec (CommRingCat.of R))) (relSubPicPresheaf c ε P))

instance (i : ι) : IsOpenImmersion
    (Scheme.LocalRepresentabilityULift.toGlued (F := relSubPicTotalSheaf hG) (f := f) hf i :
      X i ⟶ (gluedDesignation hG f hf).P) :=
  inferInstance

end glue

end AlgebraicGeometry.RelPicard
