import Mathlib
import Def.WeierstrassCurve_VeluQuotientMap
import Instance.WeierstrassCurve_VeluQuotientJInvariant

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (S : Finset (R × R))


namespace VeluQuotientJGates

def W27a3 : WeierstrassCurve ℚ := ⟨0, 0, 1, 0, 0⟩

def S₀ : Finset (ℚ × ℚ) := {(0, 0)}

end VeluQuotientJGates

end WeierstrassCurve
