import Lemma.Definitions.Def_WeierstrassCurve_FormalGroupLaw
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

theorem constantCoeff_variableChangeDenom : PowerSeries.constantCoeff (W.variableChangeDenom C) = 1 := by
  simp [variableChangeDenom, W.constantCoeff_formalW]

theorem constantCoeff_variableChangeSeries : PowerSeries.constantCoeff (W.variableChangeSeries C) = 0 := by
  simp [variableChangeSeries, W.constantCoeff_formalW]

end WeierstrassCurve

end
