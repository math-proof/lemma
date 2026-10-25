import Mathlib
import Instance.WeierstrassCurve_ConductorLevel

set_option autoImplicit false

noncomputable section

namespace WeierstrassCurve

open UniqueFactorizationMonoid

def conductorLevel (W : WeierstrassCurve ℤ) : ℕ :=
  radical W.Δ.natAbs

end WeierstrassCurve

end
