import Lemma.WeierstrassCurve.FormalGroupLaw
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Def.WeierstrassCurve_VariableChangeSeries

set_option autoImplicit false

noncomputable section

open PowerSeries

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (C : VariableChange R)


theorem constantCoeff_variableChangeDenom : PowerSeries.constantCoeff (W.variableChangeDenom C) = 1 := by
  simp [variableChangeDenom, W.constantCoeff_formalW]

theorem constantCoeff_variableChangeSeries : PowerSeries.constantCoeff (W.variableChangeSeries C) = 0 := by
  simp [variableChangeSeries, W.constantCoeff_formalW]

end WeierstrassCurve

end
