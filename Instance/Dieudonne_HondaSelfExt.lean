-- Carved from Lemma/Definitions/Def_Dieudonne_HondaSelfExt.lean: instance decls only.
import Mathlib
import Lemma.Dieudonne.DatumAndHonda
import Lemma.Dieudonne.HondaSelfExt

set_option autoImplicit false

open LinearMap Submodule Function

universe u v

namespace Deformation

namespace HondaSystem

variable {𝓞 : Type u} [CommRing 𝓞] {ℓ : 𝓞} {D : Type v} [AddCommGroup D] [Module 𝓞 D]

instance instAddCommGroupSelfExt : AddCommGroup H.selfExt :=
  inferInstanceAs (AddCommGroup (↥H.extPairs ⧸ (H.innerPairs.comap H.extPairs.subtype)))

instance instModuleSelfExt : Module 𝓞 H.selfExt :=
  inferInstanceAs (Module 𝓞 (↥H.extPairs ⧸ (H.innerPairs.comap H.extPairs.subtype)))

end HondaSystem

end Deformation
