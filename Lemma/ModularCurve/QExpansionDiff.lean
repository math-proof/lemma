import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Kaehler.Basic
import Def.ModularCurve_QExpansionDiff

set_option autoImplicit false

noncomputable section

open HahnSeries

namespace ModularCurve

section Theta

variable (L : Type*) [Field L]


variable {L} in

theorem thetaL_apply (f : LaurentSeries L) :
    thetaL L f = single (1 : ℤ) (1 : L) * LaurentSeries.derivative L f :=
  rfl

end Theta

end ModularCurve

end
