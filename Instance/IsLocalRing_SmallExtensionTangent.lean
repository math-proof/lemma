-- Carved from Lemma/Definitions/Def_IsLocalRing_SmallExtensionTangent.lean: instance decls only.
import Mathlib
import Lemma.IsLocalRing.SmallExtensionTangent

set_option autoImplicit false

noncomputable section

open IsLocalRing

namespace IsLocalRing.SmallExtension

variable {T S : Type} [CommRing T] [CommRing S] (σ : T →+* S)

instance algebra {A : Type} [CommRing A] [Algebra A T] : Algebra A (fibreProd σ) :=
  ((diag σ).comp (algebraMap A T)).toAlgebra


end IsLocalRing.SmallExtension

end
