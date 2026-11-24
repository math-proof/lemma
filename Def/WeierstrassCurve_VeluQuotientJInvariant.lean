module
public import Mathlib
public import Def.WeierstrassCurve_VeluQuotientMap
public import Instance.WeierstrassCurve_VeluQuotientJInvariant


public section

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (S : Finset (R × R))


namespace VeluQuotientJGates

def W27a3 : WeierstrassCurve ℚ := ⟨0, 0, 1, 0, 0⟩

def S₀ : Finset (ℚ × ℚ) := {(0, 0)}

end VeluQuotientJGates

end WeierstrassCurve
