import Def.WeierstrassCurve_FormalGroupLaw
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange

set_option autoImplicit false

noncomputable section

open PowerSeries

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (C : VariableChange R)

def variableChangeDenom : R⟦X⟧ :=
  1 + PowerSeries.C C.s * (PowerSeries.X - PowerSeries.C C.r * W.formalW) + PowerSeries.C C.t * W.formalW

def variableChangeSeries : R⟦X⟧ :=
  PowerSeries.C (C.u : R) * (PowerSeries.X - PowerSeries.C C.r * W.formalW) *
    PowerSeries.invOfUnit (W.variableChangeDenom C) 1

end WeierstrassCurve

end
