module

public import Mathlib
public import Structure.WeierstrassCurve_Velu
public import Def.WeierstrassCurve_VeluOrderTwo
public import Theorem.WeierstrassCurve.VeluPointMap2
public import Def.WeierstrassCurve_OddOrderSummingSet

set_option autoImplicit false

@[expose] public noncomputable section

namespace WeierstrassCurve

section XData

variable {R : Type*} [CommRing R] (V : WeierstrassCurve R)

end XData

section Field

variable {L : Type*} [Field L]

variable (L) in

abbrev CQJState : Type _ := (Σ V : WeierstrassCurve L, AddSubgroup V.toAffine.Point) × ℕ

end Field

end WeierstrassCurve

end
