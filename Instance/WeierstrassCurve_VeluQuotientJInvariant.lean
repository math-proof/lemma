-- Carved from Lemma/Definitions/Def_WeierstrassCurve_VeluQuotientJInvariant.lean: instance decls only.
import Mathlib
import Lemma.WeierstrassCurve.VeluQuotientMap
import Lemma.WeierstrassCurve.VeluQuotientJInvariant

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (S : Finset (R × R))


namespace VeluQuotientJGates

instance instIsElliptic27a4 : (W27a3.veluQuotient S₀).IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (by rw [Δ_veluQuotient_27a3]; norm_num)⟩

end VeluQuotientJGates

end WeierstrassCurve
