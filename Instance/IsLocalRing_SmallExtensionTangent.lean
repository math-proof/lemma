module
public import Mathlib
public import Theorem.Ideal.SmallExtensionTangent
public import Def.Ideal_SmallExtensionTangent
set_option autoImplicit false


public section

-- Carved from Lemma/Definitions/Def_IsLocalRing_SmallExtensionTangent.lean: instance decls only.

noncomputable section

open IsLocalRing

namespace IsLocalRing.SmallExtension

variable {T S : Type} [CommRing T] [CommRing S] (σ : T →+* S)

instance algebra {A : Type} [CommRing A] [Algebra A T] : Algebra A (fibreProd σ) :=
  ((diag σ).comp (algebraMap A T)).toAlgebra


end IsLocalRing.SmallExtension

end
