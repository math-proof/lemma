-- Carved from Lemma/Definitions/Def_GoodReductionJacobian_RelativeGroupLawKerPair.lean: instance decls only.
import Mathlib
import Abbrev.GoodReductionJacobian_RelativeGroupLawBaseChange
import Lemma.GoodReductionJacobian.RelativeGroupLawKerPair

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra NeronSpecialFibreInfra

namespace GoodReductionJacobian
namespace RelativeGroupLaw


section Properties

variable {R : Type u} [CommRing R] {A A' : Scheme.{u}}
variable (G' : RelativeGroupLaw R f') (φ : Fin 2 → SchemeHomOver f f')

instance kerPairι_isClosedImmersion [IsSeparated f'] : IsClosedImmersion (kerPairι G' φ) := by
  haveI := isClosedImmersion_one G'
  infer_instance

instance kerPairStr_locallyOfFiniteType [IsSeparated f'] [LocallyOfFiniteType f] :
    LocallyOfFiniteType (kerPairStr G' φ) := by
  infer_instance

instance kerPairStr_quasiCompact [IsSeparated f'] [QuasiCompact f] : QuasiCompact (kerPairStr G' φ) := by
  infer_instance

instance kerPairStr_isSeparated [IsSeparated f'] [IsSeparated f] : IsSeparated (kerPairStr G' φ) := by
  infer_instance

end Properties

end RelativeGroupLaw
end GoodReductionJacobian

end
