import Mathlib
import Structure.WeierstrassCurve_Velu
import Def.WeierstrassCurve_VeluOrderTwo
import Lemma.WeierstrassCurve.VeluPointMap2
import Def.WeierstrassCurve_OddOrderSummingSet

set_option autoImplicit false

noncomputable section

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
